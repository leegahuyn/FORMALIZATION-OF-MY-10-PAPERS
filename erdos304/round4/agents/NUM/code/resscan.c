/* resscan.c -- first resonance height of the prime pool P=(L/2,L] (DESIGN S4 / VKGAP-C).
 *   f(t) = sum_{p in P} p^{it},  g(t) = |f(t)|,  M = |P|.
 *   tau*_{t0}(L,eta) = min{ t >= t0 : g(t) >= (1-eta) M }.
 * Rigorous grid certificate.  Put c = log L - (log 2)/2 and l_p = log p - c, so |l_p| <= (log 2)/2.
 * g(t) = |sum_p e^{i t l_p}| (the common phase e^{itc} does not change the modulus), hence g is
 * Lipschitz with constant K = sum_p |l_p| <= M (log 2)/2   (|d/dt f_c| <= sum |l_p|; and
 * | |x|-|y| | <= |x-y|).  [The crude bound |f'| <= M log L of the brief is also valid but ~16x worse.]
 * On the grid t_i = t0 + i h every t lies within h/2 of a grid point, so
 *     g(t_i) < (1-eta)M - K h/2  for all grid points of an interval  =>  no resonance there.
 * Grid points above that lowered threshold are candidates; each is refined on [t_i-h/2, t_i+h/2]
 * with the same certificate at step h/2000 (exact long-double evaluation); the first fine point with
 * g >= (1-eta)M gives tau* (accuracy h/2000); if no fine point reaches (1-eta)M - K h/4000 the
 * candidate is certified empty; otherwise it is reported as AMBIGUOUS (never happened in our runs
 * unless printed).
 * Evaluation: z_p = e^{i t l_p} updated by rotation e^{i h l_p} in double, re-synchronised exactly
 * every CH steps from long double t*l_p (phase error ~1e-7 rad at t=1e12).
 * usage: resscan L t0 tmax secs eta1 [eta2 ...]      (stops at tmax or after secs seconds)
 * output (stdout): one line per eta:  L M eta tau* g/M  or  L M eta >T (lower bound) maxg/M
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
#define MAXM 512
static int M; static long double lp[MAXM]; static double lpd[MAXM];
static const long double TWOPI=6.283185307179586476925286766559L;

static double gexact(long double t){ /* |sum e^{i t l_p}| in long double with range reduction */
  long double re=0,im=0;
  for(int k=0;k<M;k++){ long double ph=fmodl(t*lp[k],TWOPI); re+=cosl(ph); im+=sinl(ph); }
  return (double)sqrtl(re*re+im*im);
}

int main(int argc,char**argv){
  if(argc<6){ fprintf(stderr,"usage: resscan L t0 tmax secs eta1 [eta2..]\n"); return 1; }
  int L=atoi(argv[1]); double t0=atof(argv[2]), tmax=atof(argv[3]), secs=atof(argv[4]);
  int ne=argc-5; double eta[16]; for(int i=0;i<ne;i++) eta[i]=atof(argv[5+i]);
  long double c=logl((long double)L)-logl(2.0L)/2; M=0;
  for(int p=L/2+1;p<=L;p++){ int ok=p>1; for(int q=2;q*q<=p;q++) if(p%q==0){ok=0;break;} if(ok){ lp[M]=logl((long double)p)-c; lpd[M]=(double)lp[M]; M++; } }
  double K=0; for(int k=0;k<M;k++) K+=fabs(lpd[k]);
  /* grid step: slack K h/2 = 0.02 M  (so candidates are points with g >= (1-eta-0.02)M) */
  double h=0.04*M/K;
  double thr[16], cthr[16]; int found[16]={0}; double tstar[16], gstar[16];
  for(int i=0;i<ne;i++){ thr[i]=(1-eta[i])*M; cthr[i]=thr[i]-K*h/2; }
  double cmin=1e300; for(int i=0;i<ne;i++) if(cthr[i]<cmin) cmin=cthr[i];
  const long CH=4096; double zr[MAXM],zi[MAXM],rr[MAXM],ri[MAXM];
  for(int k=0;k<M;k++){ rr[k]=cos(h*lpd[k]); ri[k]=sin(h*lpd[k]); }
  double gmax=0, tgmax=t0; long ncand=0, namb=0; double T0=now(); long double t=t0; int nleft=ne; double tend=t0;
  long long step=0;
  while(t<tmax && nleft>0){
    for(int k=0;k<M;k++){ long double ph=fmodl(t*lp[k],TWOPI); zr[k]=(double)cosl(ph); zi[k]=(double)sinl(ph); }
    for(long s=0;s<CH;s++){
      double sr=0,si=0;
      for(int k=0;k<M;k++){ sr+=zr[k]; si+=zi[k]; }
      double g2=sr*sr+si*si;
      if(g2>=cmin*cmin){
        double g=sqrt(g2); long double ti=t+(long double)s*h;
        if(g>gmax){ gmax=g; tgmax=(double)ti; }
        for(int i=0;i<ne;i++) if(!found[i] && g>=cthr[i]){
          ncand++;
          /* refine on [ti-h/2, ti+h/2] */
          int NF=2000; double hf=h/NF; int hit=0, amb=0; double gbest=0;
          for(int j=0;j<=NF;j++){ long double tf=ti-h/2+j*hf; if(tf<t0) continue; double gf=gexact(tf);
            if(gf>gbest) gbest=gf;
            if(gf>=thr[i]){ found[i]=1; tstar[i]=(double)tf; gstar[i]=gf/M; hit=1; nleft--; break; } }
          if(!hit && gbest>=thr[i]-K*hf/2) { amb=1; namb++; fprintf(stderr,"AMBIGUOUS L=%d eta=%g t=%.6Lf gbest/M=%.6f\n",L,eta[i],ti,gbest/M); }
          (void)amb;
        }
      }
      for(int k=0;k<M;k++){ double a=zr[k]*rr[k]-zi[k]*ri[k]; zi[k]=zr[k]*ri[k]+zi[k]*rr[k]; zr[k]=a; }
    }
    step+=CH; t=t0+(long double)step*h; tend=(double)t;
    if(now()-T0>secs) break;
  }
  for(int i=0;i<ne;i++){
    if(found[i]) printf("L=%d M=%d eta=%.2f tau*=%.6f g/M=%.6f  h=%.5f K=%.4f cand=%ld amb=%ld time=%.1fs\n",L,M,eta[i],tstar[i],gstar[i],h,K,ncand,namb,now()-T0);
    else printf("L=%d M=%d eta=%.2f tau*>%.6e (no resonance in [%g,%.6e]) max g/M on grid=%.6f at t=%.4f  h=%.5f K=%.4f cand=%ld amb=%ld time=%.1fs\n",L,M,eta[i],tend,t0,tend,gmax/M,tgmax,h,K,ncand,namb,now()-T0);
  }
  return 0;
}
