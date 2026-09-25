# AUD3: independent spot-check of NUM's resonance heights tau*_10(L,eta) for small M, of the
# Lipschitz constant K = sum |log p - c_L| <= (ln2/2) M, of LLL upper-bound points, and of the
# F-threshold values tau_0(eta).
import numpy as np, math, csv, os, sys
from mpmath import mp, mpf, log as mlog, cos as mcos, sin as msin, sqrt as msqrt
HERE = os.path.dirname(os.path.abspath(__file__)); R = os.path.join(HERE, '..', '..', '..')
OUT = os.path.join(HERE, '..', 'out', 'aud3_num_res.txt'); lines = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); sys.stdout.flush(); lines.append(s)
def primes(n): return [p for p in range(2, n+1) if all(p % q for q in range(2, int(p**0.5)+1))]
res = {}
with open(os.path.join(R, 'agents', 'NUM', 'data', 'resonance.csv')) as fh:
    for r in csv.DictReader(fh): res[(int(r['L']), float(r['eta']))] = r

def first_res(L, eta, tmax, h=0.002):
    P_ = [p for p in primes(L) if p > L/2]; M = len(P_)
    c = math.log(L) - math.log(2)/2
    lp = np.array([math.log(p) - c for p in P_])
    K = np.abs(lp).sum()
    thr = (1-eta)*M; t0 = 10.0; chunk = 200000
    while t0 < tmax:
        t = t0 + h*np.arange(chunk)
        g = np.abs(np.exp(1j*np.outer(t, lp)).sum(axis=1))
        hit = np.nonzero(g >= thr - K*h/2)[0]
        if len(hit):
            i = hit[0]
            # refine: fine scan of [t_i - h/2, t_i + h/2] (earlier grid points certified < thr)
            tf = t[i] - h/2 + (h/4000)*np.arange(4001)
            gf = np.abs(np.exp(1j*np.outer(tf, lp)).sum(axis=1))
            j = np.nonzero(gf >= thr)[0]
            if len(j): return M, K, tf[j[0]]
            # otherwise the candidate cell is a near miss; certify and continue
            cert = (gf < thr - K*(h/4000)/2).all()
            if not cert: return M, K, float('nan')
            t0 = t[i] + h/2; continue
        t0 = t[-1] + h
    return M, K, None

for L in [31, 43, 53, 61, 71, 73, 101]:
    for eta in [0.3, 0.2, 0.1]:
        r = res[(L, eta)]
        claim = float(r['grid_tau_star']) if r['grid_tau_star'] else None
        M, K, ts = first_res(L, eta, (claim or 1e5)*1.01 + 5)
        P(f"L={L} M={M} K/M={K/M:.4f} (<= ln2/2={math.log(2)/2:.4f}) eta={eta}: AUD3 tau*={ts:.4f}  NUM grid tau*={claim}  "
          f"log10 AUD3={math.log10(ts):.2f}  agree(rel 1e-3)={abs(ts-claim)/claim < 1e-3 if claim else None}")

P("--- LLL points: recheck g(t)/M >= 1-eta in 60-digit arithmetic (first 12 rows + random rows)")
mp.dps = 60
rows = list(csv.DictReader(open(os.path.join(R, 'agents', 'NUM', 'data', 'lll_res.csv'))))
import random; random.seed(7)
pick = rows[:12] + random.sample(rows[12:], 10)
for r in pick:
    L = int(r['L']); eta = float(r['eta']); t = mpf(r['t_found'])
    P_ = [p for p in primes(L) if p > L/2]; M = len(P_)
    re = sum(mcos(t*mlog(p)) for p in P_); im = sum(msin(t*mlog(p)) for p in P_)
    g = msqrt(re**2 + im**2)/M
    P(f"  L={L} M={M} eta={eta} t={r['t_found'][:22]} g/M={float(g):.6f} (NUM {float(r['g_over_M']):.6f}) >=1-eta: {g >= 1-eta}")

P("--- tau_0(eta): last t>=1 with |F(t)| >= 1-eta (grid 1e-5 on [1,30])")
t = np.arange(1, 30, 1e-5); Fa = np.sqrt((5-4*np.cos(t*math.log(2)))/(1+t*t))
for eta in [0.1, 0.2, 0.3]:
    idx = np.nonzero(Fa >= 1-eta)[0]
    P(f"  eta={eta}: last t = {t[idx[-1]]:.4f}")
open(OUT, 'w').write("\n".join(lines)+"\n")
