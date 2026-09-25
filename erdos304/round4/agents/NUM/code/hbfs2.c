/* hbfs2.c -- IN-PLACE variant of hbfs.c (one bitset of Lambda bits instead of two), for L=25.
 * Same mathematics: R_0={0}, R_k = (R_{k-1} + (D* u {0})) n [0,Lambda); kappa(a)=min{k: a in R_k};
 * H(L)=min{k : R_k=[0,Lambda)} (dedup theorem, baker Thm 3.2).
 *
 * In-place update, destination blocks processed in DESCENDING order.  For a destination block
 * [j0,j1) (BW words) and a shift d=64w+s, the source words are j-w, j-w-1 for j in [j0,j1):
 *   - if w <= BW they lie in [j0-BW-1, j1), which is copied (original R_{k-1} values) into a
 *     buffer C before the block is modified;
 *   - if w > BW they lie below j0, which has not been modified yet (descending order).
 * All threads work on the same block (split word range) with a barrier per block, so every read
 * sees R_{k-1}.  Skips as in hbfs.c (full destination; all-zero source window).
 * kap_small[r] = kappa(r) for r < X (X = min(Lambda, 2^xb)) is maintained for representations.
 * Checkpoint: <ck>/L<L>_R<k>.bin and <ck>/L<L>_kap<k>.bin; older levels deleted (keeps last 2).
 * usage: hbfs2 L [-t th] [-B bw] [-c ckdir] [-o outprefix] [-x xbits] [-K kapout] [-m maxlev] [-keep]
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <unistd.h>

typedef uint64_t u64;
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static u64 LAM, W; static u64 *divs; static int ndiv;
static int cmpu64(const void*a,const void*b){ u64 x=*(const u64*)a,y=*(const u64*)b; return x<y?-1:x>y; }

static void gen_divisors(int L){
  int pr[64],ex[64],np=0; LAM=1;
  for(int p=2;p<=L;p++){ int isp=1; for(int q=2;q*q<=p;q++) if(p%q==0){isp=0;break;}
    if(!isp) continue;
    int e=0; u64 pp=1; while(pp*p<=(u64)L){pp*=p;e++;} pr[np]=p; ex[np]=e; np++; LAM*=pp; }
  u64 cap=1; for(int i=0;i<np;i++) cap*=(ex[i]+1);
  u64 *all=malloc(cap*sizeof(u64)); u64 n=1; all[0]=1;
  for(int i=0;i<np;i++){ u64 m=n, pp=1; for(int e=1;e<=ex[i];e++){ pp*=pr[i]; for(u64 j=0;j<m;j++) all[n++]=all[j]*pp; } }
  qsort(all,n,sizeof(u64),cmpu64); divs=all; ndiv=(int)n-1;
}
static u64 count_ones(const u64*b,u64 lo,u64 hi){
  if(hi<=lo) return 0;
  u64 c=0, wl=lo>>6, wh=(hi-1)>>6;
  if(wl==wh){ u64 m=b[wl]>>(lo&63); int len=(int)(hi-lo); if(len<64) m&=((1ULL<<len)-1); return __builtin_popcountll(m);}
  c+=__builtin_popcountll(b[wl]>>(lo&63));
  #pragma omp parallel for reduction(+:c) schedule(static) num_threads(2) if(wh-wl>1000000)
  for(u64 j=wl+1;j<wh;j++) c+=__builtin_popcountll(b[j]);
  int r=(int)((hi-1)&63)+1; u64 m=b[wh]; if(r<64) m&=((1ULL<<r)-1); c+=__builtin_popcountll(m); return c;
}
static u64 first_zero(const u64*b,u64 lo){
  for(u64 j=lo>>6;j<W;j++){ u64 x=~b[j]; if(j==(lo>>6)) x&=~0ULL<<(lo&63); if(x){ u64 a=(j<<6)+__builtin_ctzll(x); return a<LAM?a:LAM; } }
  return LAM;
}
static void mask_tail(u64*b){ int r=(int)(LAM&63); if(r) b[W-1]&=((1ULL<<r)-1); }

#define CHW 64
static u64 *nzpref;
static void build_nzpref(const u64*A){
  u64 NCH=(W+CHW-1)/CHW; if(!nzpref) nzpref=malloc((NCH+1)*sizeof(u64)); nzpref[0]=0;
  for(u64 c=0;c<NCH;c++){ u64 lo=c*CHW, hi=lo+CHW; if(hi>W) hi=W; u64 o=0; for(u64 j=lo;j<hi;j++) o|=A[j]; nzpref[c+1]=nzpref[c]+(o!=0); }
}
static inline int src_nonzero(u64 slo,u64 shi){ if(shi<=slo) return 0; u64 c0=slo/CHW, c1=(shi-1)/CHW; return nzpref[c1+1]-nzpref[c0]!=0; }

static void level_inplace(u64*A,int nth,u64 BW,int lev){
  build_nzpref(A);
  u64 nblk=(W+BW-1)/BW; double t0=now();
  u64 *C=aligned_alloc(64,((2*BW+2)*8+63)/64*64);
  volatile int blkfull=0; u64 nfull=0;
  #pragma omp parallel num_threads(nth)
  {
    int tid=omp_get_thread_num(), nt=omp_get_num_threads();
    for(long long bi=(long long)nblk-1;bi>=0;bi--){
      u64 j0=(u64)bi*BW, j1=j0+BW; if(j1>W) j1=W;
      u64 clo=j0>BW+1?j0-BW-1:0;          /* C[i] = A[clo+i] for i < j1-clo */
      #pragma omp single
      {
        memcpy(C,A+clo,(j1-clo)*8);
        int f=1; for(u64 j=j0;j<j1;j++) if(~A[j]){f=0;break;}
        if((u64)bi==nblk-1) f=0;
        blkfull=f; if(f) nfull++;
      } /* implicit barrier */
      if(!blkfull){
        u64 len=j1-j0, q=(len+nt-1)/nt; u64 a0=j0+tid*q, a1=a0+q; if(a1>j1) a1=j1; if(a0>j1) a0=j1;
        for(int di=0;di<ndiv && a0<a1;di++){
          u64 d=divs[di], w=d>>6; int s=(int)(d&63);
          if(w>=a1) break;
          u64 js=a0>w?a0:w;
          u64 slo=js-w; if(slo>0&&s) slo--; u64 shi=a1-w;
          if(!src_nonzero(slo,shi)) continue;
          const u64 *src; if(w<=BW) src=C-clo; else src=A;   /* src[i] == original A[i] */
          u64 *dst=A;
          if(s==0){ for(u64 j=js;j<a1;j++) dst[j]|=src[j-w]; }
          else { int rs=64-s; u64 j=js; if(j==w){ dst[j]|=src[0]<<s; j++; }
            const u64 *s1=src-w, *s0=src-w-1; for(;j<a1;j++) dst[j]|=(s1[j]<<s)|(s0[j]>>rs); }
          if((di&63)==63 && (u64)bi!=nblk-1){ int f=1; for(u64 j=a0;j<a1;j++) if(~dst[j]){f=0;break;} if(f) break; }
        }
      }
      #pragma omp barrier
      if(tid==0 && nblk>=64 && (nblk-(u64)bi)%(nblk/16)==0){ double t=now()-t0; u64 dn=nblk-(u64)bi;
        fprintf(stderr,"  level %d: %llu/%llu blocks, %.1fs, eta %.1fs\n",lev,(unsigned long long)dn,(unsigned long long)nblk,t,t*(nblk-dn)/dn); }
    }
  }
  mask_tail(A); free(C);
  fprintf(stderr,"  level %d: blocks full at start %llu/%llu\n",lev,(unsigned long long)nfull,(unsigned long long)nblk);
}

static int save_file(const char*fn,const void*b,size_t n){
  char tmp[1200]; snprintf(tmp,sizeof tmp,"%s.tmp",fn); FILE*f=fopen(tmp,"wb"); if(!f) return -1;
  size_t w=fwrite(b,1,n,f); fflush(f); fsync(fileno(f)); fclose(f); if(w!=n) return -1; return rename(tmp,fn);
}
static int load_file(const char*fn,void*b,size_t n){ FILE*f=fopen(fn,"rb"); if(!f) return -1; size_t r=fread(b,1,n,f); fclose(f); return r==n?0:-1; }

int main(int argc,char**argv){
  if(argc<2){ fprintf(stderr,"usage\n"); return 1; }
  int L=atoi(argv[1]), th=2, maxlev=64, xb=30, keep=0; u64 BW=1<<15; const char*ck=NULL,*op="hbfs2",*kout=NULL;
  for(int i=2;i<argc;i++){
    if(!strcmp(argv[i],"-t")) th=atoi(argv[++i]); else if(!strcmp(argv[i],"-B")) BW=strtoull(argv[++i],0,10);
    else if(!strcmp(argv[i],"-c")) ck=argv[++i]; else if(!strcmp(argv[i],"-o")) op=argv[++i];
    else if(!strcmp(argv[i],"-x")) xb=atoi(argv[++i]); else if(!strcmp(argv[i],"-K")) kout=argv[++i];
    else if(!strcmp(argv[i],"-m")) maxlev=atoi(argv[++i]); else if(!strcmp(argv[i],"-keep")) keep=1; }
  gen_divisors(L); W=(LAM+63)/64;
  u64 X=(xb>=63)?LAM:((1ULL<<xb)<LAM?(1ULL<<xb):LAM);
  fprintf(stderr,"hbfs2 L=%d Lambda=%llu tau=%d words=%llu (%.1f MB) X=%llu threads=%d BW=%llu\n",L,(unsigned long long)LAM,ndiv+1,(unsigned long long)W,W*8/1e6,(unsigned long long)X,th,(unsigned long long)BW);
  u64 *A=aligned_alloc(64,(W*8+63)/64*64); uint8_t *kap=malloc(X);
  if(!A||!kap){ fprintf(stderr,"alloc fail\n"); return 1; }
  int k0=0; char fn[1200],fn2[1200];
  if(ck){ for(int k=maxlev;k>=1;k--){ snprintf(fn,sizeof fn,"%s/L%d_R%d.bin",ck,L,k); snprintf(fn2,sizeof fn2,"%s/L%d_kap%d.bin",ck,L,k);
      if(load_file(fn,A,W*8)==0 && load_file(fn2,kap,X)==0){ k0=k; fprintf(stderr,"resumed at level %d\n",k); break; } } }
  if(!k0){ memset(A,0,W*8); A[0]=1; memset(kap,255,X); kap[0]=0; }
  snprintf(fn,sizeof fn,"%s_levels.csv",op); FILE*fl=fopen(fn,k0?"a":"w");
  if(!k0) fprintf(fl,"L,Lambda,tau,k,ones_Rk,new_k,a_k_first_zero_of_Rkm1,lowerhalf_zeros_Rk,upperhalf_zeros_Rk,first_zero_Rk,seconds\n");
  snprintf(fn,sizeof fn,"%s_dyadic.csv",op); FILE*fd=fopen(fn,k0?"a":"w"); if(!k0) fprintf(fd,"L,k,j,lo,hi,zeros_Rk_in_lo_hi\n");
  u64 half=LAM/2, prev=count_ones(A,0,LAM);
  if(!k0){ fprintf(fl,"%d,%llu,%d,0,1,1,0,%llu,%llu,1,0\n",L,(unsigned long long)LAM,ndiv+1,(unsigned long long)(half-1),(unsigned long long)(LAM-half)); fflush(fl); }
  double T0=now();
  for(int k=k0+1;k<=maxlev;k++){
    double t=now(); u64 ak=first_zero(A,0); if(ak>=LAM) break;
    level_inplace(A,th,BW,k);
    u64 ones=count_ones(A,0,LAM), lz=half-count_ones(A,0,half), uz=(LAM-half)-count_ones(A,half,LAM), fz=first_zero(A,0);
    for(u64 r=0;r<X;r++) if(kap[r]==255 && ((A[r>>6]>>(r&63))&1)) kap[r]=(uint8_t)k;
    double dt=now()-t;
    fprintf(fl,"%d,%llu,%d,%d,%llu,%llu,%llu,%llu,%llu,%llu,%.2f\n",L,(unsigned long long)LAM,ndiv+1,k,(unsigned long long)ones,(unsigned long long)(ones-prev),(unsigned long long)ak,(unsigned long long)lz,(unsigned long long)uz,(unsigned long long)fz,dt); fflush(fl);
    for(int j=0;(1ULL<<j)<LAM;j++){ u64 lo=1ULL<<j, hi=lo<<1; if(hi>LAM) hi=LAM; u64 z=(hi-lo)-count_ones(A,lo,hi);
      fprintf(fd,"%d,%d,%d,%llu,%llu,%llu\n",L,k,j,(unsigned long long)lo,(unsigned long long)hi,(unsigned long long)z); } fflush(fd);
    fprintf(stderr,"L=%d level %d: |R_k|=%llu new=%llu a_k=%llu lowerzeros=%llu upperzeros=%llu (%.1fs, total %.1fs)\n",L,k,(unsigned long long)ones,(unsigned long long)(ones-prev),(unsigned long long)ak,(unsigned long long)lz,(unsigned long long)uz,dt,now()-T0);
    if(ck){ double ts=now(); snprintf(fn,sizeof fn,"%s/L%d_R%d.bin",ck,L,k); snprintf(fn2,sizeof fn2,"%s/L%d_kap%d.bin",ck,L,k);
      if(save_file(fn,A,W*8)||save_file(fn2,kap,X)) fprintf(stderr,"checkpoint FAILED\n");
      else { fprintf(stderr,"  checkpoint %d written (%.1fs)\n",k,now()-ts);
        if(!keep && k>=3){ snprintf(fn,sizeof fn,"%s/L%d_R%d.bin",ck,L,k-2); snprintf(fn2,sizeof fn2,"%s/L%d_kap%d.bin",ck,L,k-2); unlink(fn); unlink(fn2);} } }
    prev=ones; if(ones==LAM){ fprintf(stderr,"H(%d) = %d\n",L,k); break; }
  }
  if(kout){ FILE*f=fopen(kout,"wb"); fwrite(kap,1,X,f); fclose(f); }
  fclose(fl); fclose(fd); return 0;
}
