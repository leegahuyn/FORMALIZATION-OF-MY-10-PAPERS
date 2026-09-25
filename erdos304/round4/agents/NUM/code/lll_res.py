#!/usr/bin/env python3
"""Explicit resonances of f(t)=sum_{p in P} p^{it}, P=(L/2,L], via LLL simultaneous approximation.
Gives UPPER bounds tau*_{10}(L,eta) <= t_found (a certified point with |f(t)| >= (1-eta)M), to be
combined with the grid LOWER bounds of resscan.c.  Also a consistency check: no LLL point may lie
below a grid-certified resonance-free range.
Construction: p0 = max P, p1 = min P, y_j = (log p_j - log p0)/(2 pi).  t = n1/y1 aligns p1 with p0
exactly; the other relative phases are 2 pi (n1 a_j - n_j), a_j = y_j/y1.  Lattice rows
  b0 = (w, round(S a_2), ..., round(S a_{M-1})),  b_j = S e_j  (j = 2..M-1),  S = w*Q, w = 10^15,
so a lattice vector is (n1 w, S(n1 a_j - n_j) + O(n1)).  For each Q in a geometric range the reduced
basis vectors and their pairwise sums/differences give candidates n1; for each candidate t0=n1/y1 the
modulus |f| is maximised over t0+s, |s|<=3 (grid 1e-3, phases from mpmath at 80 digits), and the best
point is re-evaluated in mpmath.
usage: lll_res.py L [L ...]   -> prints per L and appends to data/lll_res.csv"""
import sys, os, math, csv, time
import numpy as np
import mpmath as mp
from sympy import primerange, ZZ
from sympy.polys.matrices import DomainMatrix
mp.mp.dps = 90
here = os.path.dirname(os.path.abspath(__file__))
ETAS = (0.3, 0.2, 0.1, 0.05)

def fabs_mp(t, lps):
    s = mp.mpc(0)
    for l in lps: s += mp.expj(t * l)
    return abs(s)

def run(L, qexp=np.arange(2, 41, 1.0)):
    ps = list(primerange(L // 2 + 1, L + 1)); M = len(ps)
    lps = [mp.log(p) for p in ps]
    p0 = len(ps) - 1; p1 = 0
    y = [(lps[j] - lps[p0]) / (2 * mp.pi) for j in range(M)]
    others = [j for j in range(M) if j not in (p0, p1)]
    a = [y[j] / y[p1] for j in others]
    lnp = np.array([float(l - lps[p0]) for l in lps])
    best = {e: None for e in ETAS}; bestg = {}
    ntested = 0; t0c = time.time()
    s_grid = np.arange(-3, 3, 1e-3)
    for qe in qexp:
        Q = mp.mpf(10) ** mp.mpf(qe); w = 10 ** 15; S = int(mp.nint(w * Q))
        n = len(others) + 1
        rows = [[w] + [int(mp.nint(S * aj)) for aj in a]]
        for i in range(1, n):
            r = [0] * n; r[i] = S; rows.append(r)
        B = DomainMatrix([[ZZ(x) for x in r] for r in rows], (n, n), ZZ).lll().to_Matrix()
        vecs = [list(B.row(i)) for i in range(n)]
        cands = set()
        for i in range(min(n, 8)):
            cands.add(abs(int(vecs[i][0]) // w))
            for k in range(i + 1, min(n, 8)):
                cands.add(abs(int(vecs[i][0] + vecs[k][0]) // w)); cands.add(abs(int(vecs[i][0] - vecs[k][0]) // w))
        for n1 in sorted(c for c in cands if c > 0):
            t0 = mp.mpf(n1) / abs(y[p1])
            if t0 < 10: continue
            ntested += 1
            base = np.array([float(mp.fmod(t0 * (lps[j] - lps[p0]), 2 * mp.pi)) for j in range(M)])
            g = np.abs(np.exp(1j * (base[None, :] + np.outer(s_grid, lnp))).sum(axis=1))
            i = int(np.argmax(g)); tb = t0 + mp.mpf(float(s_grid[i]))
            gb = float(fabs_mp(tb, [l - lps[p0] for l in lps]))
            for e in ETAS:
                if gb >= (1 - e) * M and (best[e] is None or tb < best[e]):
                    best[e] = tb; bestg[e] = gb / M
    res = []
    for e in ETAS:
        tb = best[e]
        res.append(dict(L=L, M=M, eta=e, t_found=(mp.nstr(tb, 15) if tb is not None else ''),
                        log10_t=(float(mp.log10(tb)) if tb is not None else ''), g_over_M=(bestg.get(e, ''))))
        print(f"L={L} M={M} eta={e}: " + (f"resonance at t={mp.nstr(tb, 15)} (log10={float(mp.log10(tb)):.3f}) |f|/M={bestg[e]:.5f}" if tb is not None else "none found"), flush=True)
    print(f"   ({ntested} candidates, {time.time()-t0c:.1f}s)", flush=True)
    return res

if __name__ == '__main__':
    out = os.path.join(here, '..', 'data', 'lll_res.csv')
    new = not os.path.exists(out)
    with open(out, 'a', newline='') as fh:
        wr = csv.DictWriter(fh, fieldnames=['L', 'M', 'eta', 't_found', 'log10_t', 'g_over_M'])
        if new: wr.writeheader()
        for L in map(int, sys.argv[1:]):
            for r in run(L): wr.writerow(r)
            fh.flush()
