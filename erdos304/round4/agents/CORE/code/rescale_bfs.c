/* CORE route (b) numerics.
 * For Lp (=L'), compute g_{Lam_{Lp}}(y) for all 0<=y<Lam_{Lp} by BFS on the sumset
 * R_k = R_{k-1} + (D* u {0})  (repetition allowed; = distinct count by dedup thm).
 * Output for every L<=Lp with Lam_L | Lam_Lp:
 *   Hres(L,Lp) = max_{1<=x<Lam_L} g_{Lam_Lp}( x * Lam_Lp/Lam_L )
 * (non-increasing in Lp, equals H(L) at Lp=L, limit = N(Lam_L)).
 * Also the level histogram of Lam_Lp.
 * usage: rescale_bfs Lp
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static uint64_t gcd(uint64_t a, uint64_t b){ while(b){uint64_t t=a%b;a=b;b=t;} return a; }
static uint64_t lam(int L){ uint64_t x=1; for(int i=2;i<=L;i++) x = x/gcd(x,i)*i; return x; }

int main(int argc, char **argv){
  int Lp = atoi(argv[1]);
  uint64_t N = lam(Lp);
  /* divisors */
  uint64_t *div = malloc(sizeof(uint64_t)*100000); int nd=0;
  for(uint64_t d=1; d*d<=N; d++) if(N%d==0){ div[nd++]=d; if(d*d!=N) div[nd++]=N/d; }
  /* proper divisors only */
  int np=0; for(int i=0;i<nd;i++) if(div[i]<N) div[np++]=div[i];
  nd=np;
  uint64_t W = (N+63)/64;
  uint64_t *R = calloc(W,8), *F = calloc(W,8), *NX = calloc(W,8);
  uint8_t *lev = malloc(N); memset(lev,255,N);
  R[0]=1; F[0]=1; lev[0]=0;
  uint64_t lastmask = (N%64)? ((1ULL<<(N%64))-1) : ~0ULL;
  int k=0; uint64_t reached=1;
  uint64_t hist[64]={0}; hist[0]=1;
  while(reached<N){
    k++;
    memset(NX,0,W*8);
    for(int t=0;t<nd;t++){
      uint64_t d=div[t], ws=d>>6, bs=d&63;
      if(bs==0){ for(uint64_t i=ws;i<W;i++) NX[i] |= F[i-ws]; }
      else {
        NX[ws] |= F[0]<<bs;
        for(uint64_t i=ws+1;i<W;i++) NX[i] |= (F[i-ws]<<bs) | (F[i-ws-1]>>(64-bs));
      }
    }
    NX[W-1] &= lastmask;
    uint64_t cnt=0;
    for(uint64_t i=0;i<W;i++){ uint64_t nw = NX[i] & ~R[i]; F[i]=nw; R[i]|=nw;
      while(nw){ int b=__builtin_ctzll(nw); lev[i*64+b]=(uint8_t)k; cnt++; nw&=nw-1; } }
    reached+=cnt; hist[k]=cnt;
    fprintf(stderr,"Lp=%d level %d new %llu reached %llu/%llu\n",Lp,k,(unsigned long long)cnt,(unsigned long long)reached,(unsigned long long)N);
  }
  printf("Lp=%d Lam=%llu tau=%d H(Lp)=%d\n",Lp,(unsigned long long)N,nd+1,k);
  printf("hist:"); for(int j=0;j<=k;j++) printf(" %llu",(unsigned long long)hist[j]); printf("\n");
  for(int L=2; L<=Lp; L++){
    uint64_t NL = lam(L); if(N%NL) continue;
    uint64_t m = N/NL; int mx=0; uint64_t argx=0; uint64_t cntmx=0;
    for(uint64_t x=1;x<NL;x++){ int v=lev[x*m]; if(v>mx){mx=v;argx=x;cntmx=0;} if(v==mx) cntmx++; }
    printf("Hres L=%d Lp=%d LamL=%llu : max=%d first_argmax_x=%llu count_at_max=%llu\n",L,Lp,(unsigned long long)NL,mx,(unsigned long long)argx,(unsigned long long)cntmx);
  }
  return 0;
}
