# VKGAP numerics (3): maximal relative divisor gaps of Lambda_L in the middle range, small L.
# For each L (where Lambda_L changes) compute all log-divisors, sort, and report
#   G_mid(L) = max log(d+/d) over consecutive divisors with log d in [log L, log Lam - log L]  (all x in [L, Lam/L])
#   G_half(L) = same restricted to [0.25 log Lam, 0.75 log Lam]
# and the pool-only quantity: max gap of {log U(E): E subset of P} within [mu-sqrt(V), mu+sqrt(V)] at q=1/2.
import numpy as np, math, time, sys
from sympy import primerange
def logdivs(L):
    arr=np.zeros(1)
    for p in primerange(2,L+1):
        a=int(math.log(L)/math.log(p)+1e-12)
        while p**(a+1)<=L: a+=1
        while p**a>L: a-=1
        arr=(arr[:,None]+np.arange(a+1)*math.log(p)).ravel()
    return arr
prev=None
print(" L   tau(Lam)   logLam   G_mid      G_half    1/G_half   | M  pool-bulk-maxgap")
for L in range(8,77):
    t0=time.time()
    ld=logdivs(L)
    if prev is not None and len(ld)==prev: continue
    prev=len(ld); ld.sort(); lam=ld[-1]
    g=np.diff(ld); lo=ld[:-1]
    m=(lo>=math.log(L))&(lo<=lam-math.log(L)); Gm=g[m].max()
    m2=(lo>=0.25*lam)&(lo<=0.75*lam); Gh=g[m2].max()
    P=list(primerange(L//2+1,L+1)); M=len(P)
    lp=np.log(np.array(P,float)); s=np.zeros(1)
    for x in lp: s=np.concatenate([s,s+x])
    s.sort(); mu=lp.sum()/2; sd=math.sqrt((lp**2).sum()/4)
    mm=(s[:-1]>=mu-sd)&(s[:-1]<=mu+sd); pg=np.diff(s)[mm].max() if mm.sum()>0 else float('nan')
    print(f"{L:3d} {len(ld):10d} {lam:8.2f} {Gm:9.5f} {Gh:10.6f} {1/Gh:9.1f}   | {M:2d} {pg:8.4f}"); sys.stdout.flush()
