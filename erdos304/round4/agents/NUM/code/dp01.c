/* dp01.c -- independent 0/1-knapsack DP for g_L(a) = least number of DISTINCT proper
 * divisors of Lambda_L summing to a (BRIEF sec.1).  Written independently of hbfs.c.
 * kappa[0]=0, kappa[n]=INF otherwise; for each proper divisor d (any order), for n from
 * Lambda-1 DOWN to d: kappa[n] = min(kappa[n], kappa[n-d]+1).  Descending order means
 * kappa[n-d] is the value before d was processed, so each divisor is used at most once.
 * For d >= 64 we process 64-byte chunks top-down: reads [n0-d,n0-d+64) lie strictly below the
 * chunk and are not yet updated in this pass, so the vectorised chunk is exact.
 * usage: dp01 L outfile   (writes kappa as uint8, INF=254)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc,char**argv){
  if(argc<3){ fprintf(stderr,"usage: dp01 L outfile\n"); return 1; }
  int L=atoi(argv[1]);
  /* Lambda and prime-power data, computed by trial division */
  uint64_t lam=1; int pr[40],ex[40],np=0;
  for(int p=2;p<=L;p++){ int ok=1; for(int q=2;q<p;q++) if(p%q==0){ok=0;break;} if(!ok) continue;
    int e=0; uint64_t pp=1; while(pp*p<=(uint64_t)L){pp*=p;e++;} pr[np]=p; ex[np]=e; np++; lam*=pp; }
  /* proper divisors: enumerate d=1..lam-1 with lam%d==0 is too slow for big lam; use exponent odometer */
  int idx[40]={0}; uint64_t *dv=malloc(4096*sizeof(uint64_t)); int nd=0;
  for(;;){ uint64_t d=1; for(int i=0;i<np;i++) for(int e=0;e<idx[i];e++) d*=pr[i];
    if(d<lam) dv[nd++]=d;
    int i=0; while(i<np && idx[i]==ex[i]){ idx[i]=0; i++; } if(i==np) break; idx[i]++; }
  uint8_t *k=malloc(lam); memset(k,254,lam); k[0]=0;
  for(int t=0;t<nd;t++){ uint64_t d=dv[t];
    if(d<64){ for(uint64_t n=lam-1;n>=d;n--){ uint8_t c=k[n-d]+1; if(c<k[n]) k[n]=c; if(n==d) break; } }
    else {
      uint64_t n=lam; /* process [n-64,n) chunks while n-64>=d */
      while(n>=d+64){ uint8_t *dst=k+n-64; const uint8_t *src=k+n-64-d;
        for(int i=0;i<64;i++){ uint8_t c=src[i]+1; dst[i]=c<dst[i]?c:dst[i]; } n-=64; }
      while(n>d){ n--; uint8_t c=k[n-d]+1; if(c<k[n]) k[n]=c; }
      if(n==d){ uint8_t c=k[0]+1; if(c<k[d]) k[d]=c; }
    }
  }
  FILE*f=fopen(argv[2],"wb"); fwrite(k,1,lam,f); fclose(f);
  int mx=0; uint64_t hist[256]={0}; for(uint64_t a=0;a<lam;a++){ hist[k[a]]++; if(k[a]>mx) mx=k[a]; }
  printf("L=%d Lambda=%llu proper_divisors=%d H=%d hist:",L,(unsigned long long)lam,nd,mx);
  for(int c=0;c<=mx;c++) printf(" %llu",(unsigned long long)hist[c]); printf("\n");
  return 0;
}
