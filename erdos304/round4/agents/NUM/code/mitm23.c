/* mitm23.c -- independent spot checks of the L=23 BFS (hbfs.c) by meet-in-the-middle.
 * (1) S3 = { d1+d2+d3 < Lambda : d_i in D* u {0} } built by direct triple enumeration
 *     (no BFS code reused); |S3| must equal |R_3| from hbfs (80 181 647), and S3 must equal
 *     the checkpoint R_3 bit for bit.
 * (2) kappa(a) <= 6  <=>  a in S3 + S3.  For a = a_7 = 3716552837 and for samples of a with
 *     R_6-bit 0 (kappa=7 by BFS) we verify that NO x in S3 has a-x in S3 (full scan), and for
 *     samples with R_6-bit 1 we verify a witness exists.  Samples: deterministic LCG.
 * usage: mitm23 R3file R6file nsamp
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <time.h>
typedef uint64_t u64;
static const u64 LAM=5354228880ULL;
static int cmp(const void*a,const void*b){ u64 x=*(u64*)a,y=*(u64*)b; return x<y?-1:x>y; }
static inline int gb(const u64*b,u64 a){ return (b[a>>6]>>(a&63))&1; }
int main(int argc,char**argv){
  u64 W=(LAM+63)/64; int ns=atoi(argv[3]);
  /* divisors of Lambda_23 = 2^4 3^2 5 7 11 13 17 19 23 by explicit exponent loops */
  u64 dv[2000]; int nd=0; int P[9]={2,3,5,7,11,13,17,19,23}, E[9]={4,2,1,1,1,1,1,1,1};
  int e[9]={0};
  for(;;){ u64 d=1; for(int i=0;i<9;i++) for(int k=0;k<e[i];k++) d*=P[i]; if(d<LAM) dv[nd++]=d;
    int i=0; while(i<9 && e[i]==E[i]){ e[i]=0; i++; } if(i==9) break; e[i]++; }
  dv[nd++]=0; qsort(dv,nd,sizeof(u64),cmp);
  printf("proper divisors + 0: %d\n",nd);
  u64 *S=calloc(W,8); double t0=clock();
  for(int i=0;i<nd;i++) for(int j=i;j<nd;j++){ u64 s2=dv[i]+dv[j]; if(s2>=LAM) break;
      for(int k=j;k<nd;k++){ u64 s=s2+dv[k]; if(s>=LAM) break; S[s>>6]|=1ULL<<(s&63); } }
  u64 c=0; for(u64 j=0;j<W;j++) c+=__builtin_popcountll(S[j]);
  printf("|S3| by triple enumeration = %llu  (%.1fs)\n",(unsigned long long)c,(clock()-t0)/CLOCKS_PER_SEC);
  int f3=open(argv[1],O_RDONLY), f6=open(argv[2],O_RDONLY);
  const u64*R3=mmap(0,W*8,PROT_READ,MAP_SHARED,f3,0), *R6=mmap(0,W*8,PROT_READ,MAP_SHARED,f6,0);
  u64 diff=0; for(u64 j=0;j<W;j++) diff+=__builtin_popcountll(R3[j]^S[j]);
  printf("S3 vs checkpoint R_3: %llu differing bits\n",(unsigned long long)diff);
  /* list of S3 elements */
  u64 *X=malloc(c*8); u64 n=0; for(u64 j=0;j<W;j++){ u64 x=S[j]; while(x){ X[n++]=(j<<6)+__builtin_ctzll(x); x&=x-1; } }
  u64 st=12345; int bad=0, n7=0, n6=0;
  for(int it=-1;it<ns;it++){
    u64 a;
    if(it<0) a=3716552837ULL;
    else { st=st*6364136223846793005ULL+1442695040888963407ULL; a=(st>>11)%LAM;
      if(it%2==0){ /* move to the next a >= LAM/2 with R6 bit 0 (kappa=7 by BFS) */
        if(a<LAM/2) a+=LAM/2; while(a<LAM && gb(R6,a)) a++; if(a>=LAM) continue; } }
    int bfs6=gb(R6,a); int wit=0;
    for(u64 i=0;i<n && X[i]<=a;i++) if(gb(S,a-X[i])){ wit=1; break; }
    int ok=(wit==bfs6); if(!ok) bad++; if(bfs6) n6++; else n7++;
    if(it<3 || !ok) printf("a=%llu BFS kappa<=6:%d  MITM (S3+S3) witness:%d  %s\n",(unsigned long long)a,bfs6,wit,ok?"agree":"DISAGREE");
  }
  printf("samples: %d with BFS kappa=7 (no MITM witness expected), %d with kappa<=6; disagreements: %d\n",n7,n6,bad);
  return 0;
}
