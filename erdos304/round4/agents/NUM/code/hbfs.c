/* hbfs.c -- exact H(L) via the dedup theorem (DESIGN S1, BRIEF sec.2).
 *
 * By the dedup theorem (baker Thm 3.2), for 0 <= a < Lambda_L the least number of
 * proper divisors of Lambda_L summing to a is the same with or without repetition.
 * Hence with R_0 = {0}, R_k = (R_{k-1} + (D* u {0})) n [0,Lambda):
 *     kappa(a) = min{k : a in R_k},   H(L) = min{k : R_k = [0,Lambda)}.
 * R_k is kept as a bitset of Lambda bits (bit a <-> integer a, LSB-first in 64-bit words).
 * One level: B = A | OR_{d in D*} (A << d), computed in destination cache blocks,
 * divisors ascending, OpenMP threads over destination blocks (no write races).
 *
 * Skips (exact, never change the result):
 *   - destination block already all ones  -> stop processing that block;
 *   - source window all zero (prefix count of nonzero 4096-bit chunks) -> skip that shift.
 * Checkpoint: each level R_k is written to <ckdir>/L<L>_R<k>.bin; on restart the highest
 * existing level is loaded and the BFS resumes from there.
 *
 * usage: hbfs L [-t threads] [-B blockwords] [-c ckdir] [-o outprefix] [-k kappafile] [-m maxlevel]
 *   -s : scatter threshold (|R_{k-1}|*#div below it -> sparse scatter step; 0 = always dense)
 *   -k : (small L only) write kappa(a), a=0..Lambda-1, as uint8 to kappafile
 * outputs: <outprefix>_levels.csv, <outprefix>_dyadic.csv, progress on stderr.
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>

typedef uint64_t u64;
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

static u64 LAM; static u64 W;           /* Lambda bits, W words */
static u64 *divs; static int ndiv;      /* proper divisors ascending */

static int cmpu64(const void*a,const void*b){ u64 x=*(const u64*)a,y=*(const u64*)b; return x<y?-1:x>y; }

static void gen_divisors(int L){
  int pr[64],ex[64],np=0;
  LAM=1;
  for(int p=2;p<=L;p++){ int isp=1; for(int q=2;q*q<=p;q++) if(p%q==0){isp=0;break;}
    if(!isp) continue; int e=0; u64 pp=1; while(pp*p<=(u64)L){pp*=p;e++;} pr[np]=p; ex[np]=e; np++; LAM*=pp; }
  u64 cap=1; for(int i=0;i<np;i++) cap*=(ex[i]+1);
  u64 *all=malloc(cap*sizeof(u64)); u64 n=1; all[0]=1;
  for(int i=0;i<np;i++){ u64 m=n; u64 pp=1; for(int e=1;e<=ex[i];e++){ pp*=pr[i]; for(u64 j=0;j<m;j++) all[n++]=all[j]*pp; } }
  qsort(all,n,sizeof(u64),cmpu64);
  divs=all; ndiv=(int)n-1;               /* drop Lambda itself (largest) */
  if(all[n-1]!=LAM){ fprintf(stderr,"divisor gen error\n"); exit(1);}
}

static inline int getbit(const u64*b,u64 a){ return (b[a>>6]>>(a&63))&1; }
static inline void setbit(u64*b,u64 a){ b[a>>6]|=1ULL<<(a&63); }

static u64 count_ones(const u64*b,u64 lo,u64 hi){ /* # ones in [lo,hi) */
  if(hi<=lo) return 0; u64 c=0; u64 wl=lo>>6, wh=(hi-1)>>6;
  if(wl==wh){ u64 m=b[wl]>>(lo&63); int len=(int)(hi-lo); if(len<64) m&=((1ULL<<len)-1); return __builtin_popcountll(m);}
  c+=__builtin_popcountll(b[wl]>>(lo&63));
  #pragma omp parallel for reduction(+:c) schedule(static) if(wh-wl>1000000)
  for(u64 j=wl+1;j<wh;j++) c+=__builtin_popcountll(b[j]);
  int r=(int)((hi-1)&63)+1; u64 m=b[wh]; if(r<64) m&=((1ULL<<r)-1); c+=__builtin_popcountll(m);
  return c;
}
static u64 first_zero(const u64*b,u64 lo){ /* smallest a>=lo with bit 0, or LAM */
  for(u64 j=lo>>6;j<W;j++){ u64 x=~b[j]; if(j==(lo>>6)) x&=~0ULL<<(lo&63); if(x){ u64 a=(j<<6)+__builtin_ctzll(x); return a<LAM?a:LAM; } }
  return LAM;
}
static void mask_tail(u64*b){ int r=(int)(LAM&63); if(r) b[W-1]&=((1ULL<<r)-1); }

/* one BFS level: B = A | OR_d (A<<d) restricted to [0,LAM) */
static u64 *nzpref; static u64 NCH; /* chunks of 64 words */
#define CHW 64
static void build_nzpref(const u64*A){
  NCH=(W+CHW-1)/CHW; if(!nzpref) nzpref=malloc((NCH+1)*sizeof(u64));
  nzpref[0]=0;
  for(u64 c=0;c<NCH;c++){ u64 lo=c*CHW, hi=lo+CHW; if(hi>W) hi=W; u64 o=0; for(u64 j=lo;j<hi;j++) o|=A[j]; nzpref[c+1]=nzpref[c]+(o!=0); }
}
static inline int src_nonzero(u64 slo,u64 shi){ /* any nonzero word in A[slo,shi) ? */
  if(shi<=slo) return 0; u64 c0=slo/CHW, c1=(shi-1)/CHW; return nzpref[c1+1]-nzpref[c0]!=0; }

static void level(const u64*restrict A,u64*restrict B,int nthreads,u64 BW,int lev){
  build_nzpref(A);
  u64 nblk=(W+BW-1)/BW; double t0=now(); volatile u64 done=0; u64 skipped_full=0;
  #pragma omp parallel for schedule(dynamic,1) num_threads(nthreads) reduction(+:skipped_full)
  for(u64 bi=0;bi<nblk;bi++){
    u64 j0=bi*BW, j1=j0+BW; if(j1>W) j1=W;
    u64 *restrict dst=B;
    memcpy(dst+j0,A+j0,(j1-j0)*8);
    int full=1; for(u64 j=j0;j<j1;j++) if(~dst[j]){full=0;break;}
    if(bi==nblk-1){ /* last block: full means all bits < LAM set */ full=0; }
    if(full){ skipped_full++; goto next; }
    for(int di=0;di<ndiv;di++){
      u64 d=divs[di]; u64 w=d>>6; int s=(int)(d&63);
      if(w>=j1) break;                    /* shift beyond this block: all larger d too */
      u64 js=j0>w?j0:w;                   /* dst words js..j1-1 read src js-w(-1).. */
      u64 slo=js-w; if(slo>0 && s) slo--; u64 shi=j1-w;
      if(!src_nonzero(slo,shi)) continue;
      const u64*restrict src=A;
      if(s==0){
        for(u64 j=js;j<j1;j++) dst[j]|=src[j-w];
      } else {
        int rs=64-s; u64 j=js;
        if(j==w){ dst[j]|=src[0]<<s; j++; }
        const u64*restrict s1=src-w; const u64*restrict s0=src-w-1;
        for(;j<j1;j++) dst[j]|=(s1[j]<<s)|(s0[j]>>rs);
      }
      if((di&63)==63){ int f=1; for(u64 j=j0;j<j1;j++) if(~dst[j]){f=0;break;} if(f && bi!=nblk-1) break; }
    }
  next:
    ;
    u64 dn=__atomic_add_fetch(&done,1,__ATOMIC_RELAXED);
    if(nblk>=64 && dn%(nblk/16)==0){ double t=now()-t0; fprintf(stderr,"  level %d: %llu/%llu blocks, %.1fs, eta %.1fs\n",lev,(unsigned long long)dn,(unsigned long long)nblk,t,t*(nblk-dn)/dn); }
  }
  mask_tail(B);
  fprintf(stderr,"  level %d: blocks skipped as full at start: %llu/%llu\n",lev,(unsigned long long)skipped_full,(unsigned long long)nblk);
}

static void level_scatter(const u64*A,u64*B){ /* for very sparse A */
  memcpy(B,A,W*8);
  for(u64 j=0;j<W;j++){ u64 x=A[j]; while(x){ int t=__builtin_ctzll(x); x&=x-1; u64 a=(j<<6)+t;
      for(int di=0;di<ndiv;di++){ u64 s=a+divs[di]; if(s>=LAM) break; setbit(B,s);} } }
}

static int save_level(const char*dir,int L,int k,const u64*b){
  char fn[1024],tmp[1100]; snprintf(fn,sizeof fn,"%s/L%d_R%d.bin",dir,L,k); snprintf(tmp,sizeof tmp,"%s.tmp",fn);
  FILE*f=fopen(tmp,"wb"); if(!f) return -1; size_t w=fwrite(b,8,W,f); fflush(f); fsync(fileno(f)); fclose(f);
  if(w!=W) return -1; rename(tmp,fn); return 0;
}
static int load_level(const char*dir,int L,int k,u64*b){
  char fn[1024]; snprintf(fn,sizeof fn,"%s/L%d_R%d.bin",dir,L,k); FILE*f=fopen(fn,"rb"); if(!f) return -1;
  size_t r=fread(b,8,W,f); fclose(f); return r==W?0:-1;
}

int main(int argc,char**argv){
  if(argc<2){ fprintf(stderr,"usage: hbfs L [-t th] [-B bw] [-c ckdir] [-o outprefix] [-k kappafile] [-m maxlev]\n"); return 1; }
  int L=atoi(argv[1]); int th=2; u64 BW=1<<15; const char*ck=NULL; const char*op="hbfs"; const char*kf=NULL; int maxlev=64; u64 scth=100000000ULL;
  for(int i=2;i<argc;i++){
    if(!strcmp(argv[i],"-t")) th=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-B")) BW=strtoull(argv[++i],0,10);
    else if(!strcmp(argv[i],"-c")) ck=argv[++i];
    else if(!strcmp(argv[i],"-o")) op=argv[++i];
    else if(!strcmp(argv[i],"-k")) kf=argv[++i];
    else if(!strcmp(argv[i],"-m")) maxlev=atoi(argv[++i]);
    else if(!strcmp(argv[i],"-s")) scth=strtoull(argv[++i],0,10);
  }
  gen_divisors(L); W=(LAM+63)/64;
  fprintf(stderr,"L=%d Lambda=%llu tau=%d proper=%d words=%llu (%.1f MB/bitset) threads=%d BW=%llu\n",L,(unsigned long long)LAM,ndiv+1,ndiv,(unsigned long long)W,W*8/1e6,th,(unsigned long long)BW);
  u64*A=aligned_alloc(64,((W*8+63)/64)*64), *B=aligned_alloc(64,((W*8+63)/64)*64);
  if(!A||!B){ fprintf(stderr,"alloc failed\n"); return 1; }
  uint8_t*kap=NULL; if(kf){ kap=malloc(LAM); memset(kap,255,LAM); }
  int k0=0;
  if(ck){ for(int k=maxlev;k>=1;k--){ if(load_level(ck,L,k,A)==0){ k0=k; fprintf(stderr,"resumed from checkpoint level %d\n",k); break; } } }
  if(k0==0){ memset(A,0,W*8); A[0]=1; if(kap) kap[0]=0; }
  if(kap && k0>0){ fprintf(stderr,"-k requires a fresh run\n"); return 1; }
  char fn[1200]; snprintf(fn,sizeof fn,"%s_levels.csv",op);
  FILE*fl=fopen(fn,k0?"a":"w"); if(k0==0) fprintf(fl,"L,Lambda,tau,k,ones_Rk,new_k,a_k_first_zero_of_Rkm1,lowerhalf_zeros_Rk,upperhalf_zeros_Rk,first_zero_Rk,seconds\n");
  snprintf(fn,sizeof fn,"%s_dyadic.csv",op);
  FILE*fd=fopen(fn,k0?"a":"w"); if(k0==0) fprintf(fd,"L,k,j,lo,hi,zeros_Rk_in_[lo,hi)\n");
  u64 half=LAM/2;
  u64 prevones=count_ones(A,0,LAM);
  if(k0==0){ fprintf(fl,"%d,%llu,%d,0,1,1,0,%llu,%llu,1,0\n",L,(unsigned long long)LAM,ndiv+1,(unsigned long long)(half-1),(unsigned long long)(LAM-half)); fflush(fl); }
  double T0=now();
  for(int k=k0+1;k<=maxlev;k++){
    double t=now();
    u64 ak=first_zero(A,0);              /* smallest a not in R_{k-1}: kappa(a_k)=k */
    if(ak>=LAM){ fprintf(stderr,"already full\n"); break; }
    if(prevones*(u64)ndiv<scth) level_scatter(A,B); else level(A,B,th,BW,k);
    u64 ones=count_ones(B,0,LAM);
    u64 lz=half-count_ones(B,0,half), uz=(LAM-half)-count_ones(B,half,LAM);
    u64 fz=first_zero(B,0);
    double dt=now()-t;
    fprintf(fl,"%d,%llu,%d,%d,%llu,%llu,%llu,%llu,%llu,%llu,%.2f\n",L,(unsigned long long)LAM,ndiv+1,k,(unsigned long long)ones,(unsigned long long)(ones-prevones),(unsigned long long)ak,(unsigned long long)lz,(unsigned long long)uz,(unsigned long long)fz,dt); fflush(fl);
    for(int j=0;(1ULL<<j)<LAM;j++){ u64 lo=1ULL<<j, hi=lo<<1; if(hi>LAM) hi=LAM; u64 z=(hi-lo)-count_ones(B,lo,hi);
      fprintf(fd,"%d,%d,%d,%llu,%llu,%llu\n",L,k,j,(unsigned long long)lo,(unsigned long long)hi,(unsigned long long)z); }
    fflush(fd);
    if(kap){ for(u64 j=0;j<W;j++){ u64 x=B[j]&~A[j]; while(x){ int b=__builtin_ctzll(x); x&=x-1; kap[(j<<6)+b]=(uint8_t)k; } } }
    fprintf(stderr,"L=%d level %d: |R_k|=%llu new=%llu a_k=%llu lowerzeros=%llu upperzeros=%llu  (%.1fs, total %.1fs)\n",L,k,(unsigned long long)ones,(unsigned long long)(ones-prevones),(unsigned long long)ak,(unsigned long long)lz,(unsigned long long)uz,dt,now()-T0);
    if(ck){ double ts=now(); if(save_level(ck,L,k,B)) fprintf(stderr,"checkpoint write FAILED\n"); else fprintf(stderr,"  checkpoint level %d written (%.1fs)\n",k,now()-ts); }
    u64*tmp=A; A=B; B=tmp; prevones=ones;
    if(ones==LAM){ fprintf(stderr,"H(%d) = %d\n",L,k); break; }
  }
  fclose(fl); fclose(fd);
  if(kap){ FILE*f=fopen(kf,"wb"); fwrite(kap,1,LAM,f); fclose(f); }
  return 0;
}
