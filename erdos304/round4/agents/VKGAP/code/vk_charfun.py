# VKGAP numerics (1): prime-pool exponential sums A(tau)=sum_{p in (L/2,L]} p^{i tau},
# pair-argument bound, smoothed (trapezoid) sums W(tau), and the (NR') quantity.
import numpy as np, math, sys, time
def primes_upto(N):
    s=np.ones(N+1,bool); s[:2]=False
    for i in range(2,int(N**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]
PR=primes_upto(10**6)
kappa=0.05
def w(u):
    u=np.asarray(u,float); r=np.zeros_like(u)
    m=(u>0.5)&(u<0.5+kappa); r[m]=(u[m]-0.5)/kappa
    m=(u>=0.5+kappa)&(u<=1-kappa); r[m]=1
    m=(u>1-kappa)&(u<1); r[m]=(1-u[m])/kappa
    return r
def sums(lp,taus,weights=None,chunk=2000):
    out=np.empty(len(taus),complex)
    for i in range(0,len(taus),chunk):
        t=taus[i:i+chunk]
        E=np.exp(1j*np.outer(t,lp))
        out[i:i+chunk]=E@(np.ones(len(lp)) if weights is None else weights)
    return out
v0=0.0059; c2=2*v0/math.pi**2
for L in [10**4,10**5,10**6]:
    t0=time.time()
    P=PR[(PR>L//2)&(PR<=L)]; M=len(P); lp=np.log(P.astype(float))
    var=lp.var()
    # pair-argument range (0, pi/log2]
    tau=np.linspace(1e-3,math.pi/math.log(2),3000 if L<10**6 else 1500)
    A=sums(lp,tau)
    ratio=(M-np.abs(A))/(tau**2*M)
    ratioRe=(M-A.real)/(tau**2*M)
    # large tau
    hi=2000 if L<=10**5 else 400
    step=0.05
    tl=np.arange(4.0,hi,step)
    Al=sums(lp,tl)
    wt=w(P/L)*lp
    Wl=sums(lp,tl,wt)
    W0=wt.sum()
    nrq=(M-Al.real)/M   # sum(1-cos)/M
    Fb=3/np.sqrt(1+tl**2)
    print(f"L={L} M={M} M*log(L)/L={M*math.log(L)/L:.4f} Var_P(log p)={var:.5f} (limit 0.039069; proof uses v0={v0})")
    print(f"  pair range: min (M-|A|)/(tau^2 M)={ratio.min():.5f} >= (2/pi^2)Var_P={2*var/math.pi**2:.5f}? {ratio.min()>=2*var/math.pi**2-1e-12}; >= c2={c2:.5f}? {ratio.min()>=c2}")
    print(f"  min (M-Re A)/(tau^2 M) on (0,4.53]={ratioRe.min():.5f}")
    print(f"  tau in [4,{hi}] step {step}: max|A|/M={np.abs(Al).max()/M:.4f} at tau={tl[np.abs(Al).argmax()]:.2f}; max(|A|/M-3/sqrt(1+tau^2))={(np.abs(Al)/M-Fb).max():.4f}")
    print(f"  smoothed: max|W(tau)|/W(0)={np.abs(Wl).max()/W0:.4f} (proof bound 0.4138/0.45=0.9196 + o(1)); min sum(1-cos)/M={nrq.min():.4f} (proof needs >=1/15=0.0667)")
    # lattice dip illustration: exponent bound n*(1-Re A/M) at tau=2pi/log L for n=(log L)^2
    tt=2*math.pi/math.log(L); a=sums(lp,np.array([tt]))[0]
    print(f"  lattice: at tau=2pi/logL={tt:.4f}: 1-Re A/M={1-a.real/M:.5f}, 1-|A|/M={1-abs(a)/M:.5f}, compare c*tau^2 with Var_P: {(2/math.pi**2)*var*tt**2:.5f}")
    print(f"  time {time.time()-t0:.1f}s"); sys.stdout.flush()
