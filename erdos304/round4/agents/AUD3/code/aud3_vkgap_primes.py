# AUD3: independent numerics for VKGAP: prime-pool sums, (NR') quantity with a Lipschitz
# certificate, pair-argument ratio, smoothed sums, cofactor lemma (exact integers), divisor gaps.
# Output: ../out/aud3_vkgap_primes.txt
import numpy as np, math, time, sys, os
from itertools import product
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'out', 'aud3_vkgap_primes.txt')
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); sys.stdout.flush(); lines.append(s)

def sieve(N):
    s = np.ones(N+1, bool); s[:2] = False
    for i in range(2, int(N**0.5)+1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
PR = sieve(10**6)

def csum(lp, taus, wts=None, chunk=256):
    res = np.empty(len(taus), complex)
    wv = np.ones(len(lp)) if wts is None else wts
    for i in range(0, len(taus), chunk):
        t = taus[i:i+chunk]
        res[i:i+chunk] = np.exp(1j*np.outer(t, lp)) @ wv
    return res

def trap(u, k=0.05):
    u = np.asarray(u, float)
    return np.clip(np.minimum((u-0.5)/k, (1-u)/k), 0, 1)

for L, hi, h in [(10**4, 2000.0, 0.005), (10**5, 600.0, 0.01), (10**6, 60.0, 0.002)]:
    t0 = time.time()
    p = PR[(PR > L//2) & (PR <= L)]; M = len(p); lp = np.log(p.astype(float)); th = lp.sum()
    P(f"--- L={L} M={M} theta_P/L={th/L:.4f} M logL/L={M*math.log(L)/L:.4f}")
    P(f"  Var_P(log p)={lp.var():.5f}; v0=0.0059")
    A1 = csum(lp, np.array([1.0]))[0]
    P(f"  |A(1)|/M={abs(A1)/M:.5f} (|F(1)|=0.980572)")
    # pair argument on (0, pi/log 2]
    tau = np.linspace(1e-3, math.pi/math.log(2), 2000)
    A = csum(lp, tau)
    rat = (M-np.abs(A))/(tau**2*M)
    P(f"  min_(0,pi/log2] (M-|A|)/(tau^2 M) = {rat.min():.5f}  vs (2/pi^2)Var = {2*lp.var()/math.pi**2:.5f}")
    # NR' quantity on [4,hi] with Lipschitz certificate: |d/dtau sum cos(tau log p)| <= theta_P
    tl = np.arange(4.0, hi+h, h)
    Al = csum(lp, tl)
    q = (M - Al.real)/M
    cert = q.min() - (h/2)*th/M
    P(f"  [4,{hi}] step {h}: min sum(1-cos)/M = {q.min():.4f} at tau={tl[q.argmin()]:.3f}; certified lower bound = {cert:.4f} (>1/15={1/15:.4f}: {cert>1/15})")
    P(f"  max |A|/M on grid = {np.abs(Al).max()/M:.4f} at tau={tl[np.abs(Al).argmax()]:.3f}; 3/sqrt(17)={3/math.sqrt(17):.4f}")
    wt = trap(p/L)*lp
    W = csum(lp, tl, wt); W0 = wt.sum()
    P(f"  smoothed: W(0)/L={W0/L:.4f} (tilde w(1)=0.45); max|W(tau)|/L={np.abs(W).max()/L:.4f} (<= |tilde w(1+i tau)|+eps; bound 0.4138)")
    lower = (W0 - W.real)/math.log(L)/M
    P(f"  smoothed minorant (W(0)-Re W)/(M log L): min={lower.min():.4f} (>=1/15 needed asymptotically)")
    tt = 2*math.pi/math.log(L); a = csum(lp, np.array([tt]))[0]
    P(f"  lattice tau=2pi/logL={tt:.4f}: 1-|A|/M={1-abs(a)/M:.5f}, 0.0196 tau^2={0.0196*tt*tt:.5f}")
    P(f"  time {time.time()-t0:.1f}s")

# ---- cofactor lemma, exact integers
def lam_fact(L):
    f = {}
    for q in PR[PR <= L]:
        q = int(q); a = 0; v = 1
        while v*q <= L: v *= q; a += 1
        f[q] = a
    return f
def divisors_from(f):
    ds = [1]
    for q, a in f.items():
        ds = [d*q**e for d in ds for e in range(a+1)]
    return ds
P("--- cofactor lemma: max consecutive-divisor ratio of Q_y = Lam_L / prod_{y/2<p<=y} p")
worst_all = 0; cases = 0
for L in [16, 20, 24, 30, 36, 42]:
    f = lam_fact(L)
    for y in range(4, L+1):
        g = dict(f)
        for q in list(g):
            if y/2 < q <= y: g[q] -= 1
        ds = np.array(sorted(divisors_from(g)), dtype=np.int64)
        r = (ds[1:] > 2*ds[:-1]).sum()
        cases += 1
        if r: P(f"  FAIL L={L} y={y}")
        worst_all = max(worst_all, float((ds[1:]/ds[:-1]).max()))
f = lam_fact(60)
for y in [4, 8, 16, 30, 45, 60]:
    g = dict(f)
    for q in list(g):
        if y/2 < q <= y: g[q] -= 1
    ds = sorted(divisors_from(g))
    bad = sum(1 for i in range(len(ds)-1) if ds[i+1] > 2*ds[i]); cases += 1
    worst_all = max(worst_all, max(ds[i+1]/ds[i] for i in range(len(ds)-1)))
    if bad: P(f"  FAIL L=60 y={y}")
P(f"  {cases} (L,y) cases, y in [4,L]: max ratio = {worst_all}  (<=2 required)")

# ---- divisor gaps (exact) for comparison with VKGAP (N3)
P("--- max consecutive log-gap of divisors of Lam_L with log d in [0.25 logLam, 0.75 logLam]")
for L in [19, 29, 43]:
    ds = sorted(divisors_from(lam_fact(L))); lam = ds[-1]; LL = math.log(lam)
    best = 0
    for i in range(len(ds)-1):
        ld = math.log(ds[i])
        if 0.25*LL <= ld <= 0.75*LL:
            best = max(best, math.log(ds[i+1]/ds[i]))
    P(f"  L={L} tau={len(ds)} 1/G_half={1/best:.1f}")
open(OUT, 'w').write("\n".join(lines)+"\n")
