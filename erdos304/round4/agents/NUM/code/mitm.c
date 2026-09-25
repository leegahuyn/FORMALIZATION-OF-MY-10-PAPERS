/* mitm.c -- BFS-independent spot checks for general L (used for L=25).
 * S3 = {d1+d2+d3 < Lambda : d_i in D* u {0}} by direct triple enumeration; prints |S3|
 * (to compare with |R_3| of the BFS).  For each test value a (from a file, one per line):
 * prints whether a in S3+S3 (<=> kappa(a) <= 6), by scanning all x in S3, x <= a.
 * usage: mitm L testfile
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
typedef uint64_t u64;
static int cmp(const void*a,const void*b){ u64 x=*(u64*)a,y=*(u64*)b; return x<y?-1:x>y; }
int main(int argc,char**argv){
  int L=atoi(argv[1]);
  int P[20],E[20],np=0; u64 LAM=1;
  for(int p=2;p<=L;p++){ int ok=1; for(int q=2;q<p;q++) if(p%q==0){ok=0;break;} if(!ok) continue;
    int e=0; u64 pp=1; while(pp*p<=(u64)L){pp*=p;e++;} P[np]=p; E[np]=e; np++; LAM*=pp; }
  u64 *dv=malloc(20000*8); int nd=0; int e[20]={0};
  for(;;){ u64 d=1; for(int i=0;i<np;i++) for(int k=0;k<e[i];k++) d*=P[i]; if(d<LAM) dv[nd++]=d;
    int i=0; while(i<np && e[i]==E[i]){ e[i]=0; i++; } if(i==np) break; e[i]++; }
  dv[nd++]=0; qsort(dv,nd,sizeof(u64),cmp);
  u64 W=(LAM+63)/64; u64 *S=calloc(W,8); if(!S){ fprintf(stderr,"alloc\n"); return 1; }
  double t0=clock();
  for(int i=0;i<nd;i++) for(int j=i;j<nd;j++){ u64 s2=dv[i]+dv[j]; if(s2>=LAM) break;
      for(int k=j;k<nd;k++){ u64 s=s2+dv[k]; if(s>=LAM) break; S[s>>6]|=1ULL<<(s&63); } }
  u64 c=0; for(u64 j=0;j<W;j++) c+=__builtin_popcountll(S[j]);
  printf("L=%d Lambda=%llu proper divisors=%d |S3|=%llu (%.1fs)\n",L,(unsigned long long)LAM,nd-1,(unsigned long long)c,(clock()-t0)/CLOCKS_PER_SEC);
  FILE*f=fopen(argv[2],"r"); unsigned long long a;
  while(fscanf(f,"%llu",&a)==1){
    int wit=0; u64 xw=0;
    for(u64 j=0;j<W && (j<<6)<=a && !wit;j++){ u64 x=S[j]; while(x){ u64 v=(j<<6)+__builtin_ctzll(x); x&=x-1; if(v>a) break;
        u64 r=a-v; if((S[r>>6]>>(r&63))&1){ wit=1; xw=v; break; } } }
    printf("a=%llu  in S3+S3 (kappa<=6): %s", a, wit?"YES":"NO");
    if(wit) printf("  (x=%llu, a-x=%llu)",(unsigned long long)xw,(unsigned long long)(a-xw));
    printf("\n"); fflush(stdout);
  }
  return 0;
}
