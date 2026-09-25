/* CORE route (c) numerics: additive energy E_2(A) = #{(a1,a2,a3,a4) in A^4 : a1+a2=a3+a4}
 * for A = D*_L (proper divisors of Lam_L) and A = {d | Lam_L : sqrt(Lam) <= d < Lam}.
 * Trivial solutions: 2N^2 - N.  Prints ratio E/(2N^2-N) and the number of
 * nontrivial solutions with a1=a2 (i.e. d+d = u+v, the dedup identities).
 * usage: energy2 L
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

static uint64_t gcd(uint64_t a, uint64_t b){ while(b){uint64_t t=a%b;a=b;b=t;} return a; }
static uint64_t lam(int L){ uint64_t x=1; for(int i=2;i<=L;i++) x = x/gcd(x,i)*i; return x; }
static int cmpu(const void*a,const void*b){ uint64_t x=*(const uint64_t*)a,y=*(const uint64_t*)b; return x<y?-1:x>y; }

static void energy(uint64_t *A, long N, const char *name, int L){
  long np = N*(N+1)/2;
  uint64_t *S = malloc(sizeof(uint64_t)*np); long c=0;
  for(long i=0;i<N;i++) for(long j=i;j<N;j++) S[c++] = ((A[i]+A[j])<<1) | (i<j?1:0);
  qsort(S,np,8,cmpu);
  /* E = sum_s r(s)^2, r(s)= sum of weights (2 for i<j, 1 for i=j) */
  long double E=0; long double Ediag=0; /* nontrivial with a1=a2: sum over s of (#diag pairs at s)*(r(s)-1)... */
  long i=0; long maxr=0;
  while(i<np){
    long j=i; uint64_t s=S[i]>>1; long r=0, nd=0;
    while(j<np && (S[j]>>1)==s){ if(S[j]&1) r+=2; else {r+=1; nd++;} j++; }
    E += (long double)r*r;
    /* ordered quadruples with a1=a2=d (diag) and (a3,a4) != (d,d): nd*(r-1) ; count both sides symmetric */
    Ediag += (long double)nd*(r-1);
    if(r>maxr) maxr=r;
    i=j;
  }
  long double triv = 2.0L*N*N - N;
  printf("L=%d %s N=%ld E=%.0Lf trivial=%.0Lf ratio=%.6Lf nontriv/N^2=%.6Lf diag_nontriv/N^2=%.6Lf max_r=%ld\n",
         L,name,N,E,triv,E/triv,(E-triv)/((long double)N*N),Ediag/((long double)N*N),maxr);
  free(S);
}

int main(int argc,char**argv){
  int L=atoi(argv[1]); uint64_t Lam=lam(L);
  uint64_t *D=malloc(sizeof(uint64_t)*200000); long nd=0;
  for(uint64_t d=1; d*d<=Lam; d++) if(Lam%d==0){ D[nd++]=d; if(d*d!=Lam) D[nd++]=Lam/d; }
  qsort(D,nd,8,cmpu);
  long N=nd-1; /* proper */
  energy(D,N,"all_proper",L);
  double sq=sqrt((double)Lam); long st=0; while(st<N && (double)D[st]<sq) st++;
  energy(D+st,N-st,"large(>=sqrtLam)",L);
  /* top window [Lam/64, Lam) */
  long st2=0; while(st2<N && D[st2]*64<Lam) st2++;
  energy(D+st2,N-st2,"top[Lam/64,Lam)",L);
  return 0;
}
