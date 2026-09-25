// AUD3: independent meet-in-the-middle membership tests for kappa_L (written from scratch).
// S3 = { d1+d2+d3 : di in D* u {0} } (sums of <= 3 proper divisors, repetition allowed).
// By the dedup theorem, kappa(a) <= 3+k  <=>  a in S3 + S_k  (S_k = sums of <= k divisors).
// usage: aud3_mitm L A k1 a1 k2 a2 ...   (bitset of S3 on [0,A]; each test: is a_i in S3+S_{k_i}?)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned long long u64;
static u64 *bits; static u64 A;
static inline int getb(u64 x){ return (bits[x>>6]>>(x&63))&1ULL; }
static int cmp(const void*a,const void*b){ u64 x=*(u64*)a,y=*(u64*)b; return x<y?-1:x>y; }
int main(int argc,char**argv){
  int L=atoi(argv[1]); A=strtoull(argv[2],0,10);
  u64 lam=1; int pr[]={2,3,5,7,11,13,17,19,23,29,31,37,41,43,47}; int np=0; int ex[16];
  for(int i=0;i<15&&pr[i]<=L;i++){ u64 q=pr[i],v=1; int e=0; while(v*q<=(u64)L){v*=q;e++;} ex[i]=e; lam*=v; np=i+1; }
  // divisors
  u64 *d=malloc(sizeof(u64)*100000); int n=1; d[0]=1;
  for(int i=0;i<np;i++){ int m=n; u64 pw=1; for(int e=1;e<=ex[i];e++){ pw*=pr[i]; for(int j=0;j<m;j++) d[n++]=d[j]*pw; } }
  qsort(d,n,sizeof(u64),cmp);
  // v = {0} u proper divisors
  u64 *v=malloc(sizeof(u64)*(n+1)); int nv=0; v[nv++]=0; for(int i=0;i<n;i++) if(d[i]<lam) v[nv++]=d[i];
  printf("L=%d Lam=%llu tau=%d |D* u {0}|=%d A=%llu\n",L,lam,n,nv,A);
  u64 words=(A>>6)+1; bits=calloc(words,8); if(!bits){printf("alloc fail\n");return 1;}
  for(int i=0;i<nv;i++){ u64 si=v[i]; if(si>A) break;
    for(int j=i;j<nv;j++){ u64 sj=si+v[j]; if(sj>A) break;
      for(int k=j;k<nv;k++){ u64 s=sj+v[k]; if(s>A) break; bits[s>>6]|=1ULL<<(s&63); } } }
  u64 cnt=0; for(u64 w=0;w<words;w++) cnt+=__builtin_popcountll(bits[w]);
  // remove bits beyond A (none set by construction)
  printf("|S3 cap [0,A]| = %llu\n",cnt); fflush(stdout);
  for(int t=3;t+1<argc;t+=2){
    int k=atoi(argv[t]); u64 a=strtoull(argv[t+1],0,10); int found=0; u64 w1=0,w2=0,w3=0;
    if(a>A){ printf("a=%llu > A, skipped\n",a); continue; }
    if(k==0){ found=getb(a); }
    else if(k==1){ for(int i=0;i<nv&&v[i]<=a;i++) if(getb(a-v[i])){found=1;w1=v[i];break;} }
    else if(k==2){ for(int i=0;i<nv&&!found;i++){ if(v[i]>a) break; for(int j=i;j<nv;j++){ u64 s=v[i]+v[j]; if(s>a) break; if(getb(a-s)){found=1;w1=v[i];w2=v[j];break;} } } }
    else if(k==3){ for(u64 s=0;s<=a;s++){ u64 w=bits[s>>6]; if(!w){ s|=63; continue; } if(((w>>(s&63))&1ULL) && getb(a-s)){found=1;w1=s;w2=a-s;break;} } }
    printf("test: a=%llu in S3+S%d ? %s  (=> kappa(a) %s %d)",a,k,found?"YES":"NO",found?"<=":">=",found?3+k:4+k);
    if(found) printf("  witness parts %llu %llu %llu",w1,w2,w3);
    printf("\n"); fflush(stdout);
  }
  return 0;
}
