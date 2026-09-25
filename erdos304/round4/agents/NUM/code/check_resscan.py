#!/usr/bin/env python3
"""Independent brute-force check of resscan.c for small pools: dense numpy grid (step 2e-4) on
[10, 1.02*tau*] ; reports first grid point with |f|>=(1-eta)M (must agree with resscan to ~1e-3)."""
import numpy as np, sys
from sympy import primerange
res = {}
for line in open(sys.argv[1]):
    if 'tau*=' in line and '>' not in line.split('tau*')[1][:2]:
        f = dict(x.split('=') for x in line.split() if '=' in x)
        res[(int(f['L']), float(f['eta']))] = float(f['tau*'])
for (L, eta), ts in sorted(res.items()):
    if ts > 5e4: continue
    ps = np.array(list(primerange(L // 2 + 1, L + 1)), dtype=float); M = len(ps)
    lp = np.log(ps)
    t = np.arange(10.0, ts * 1.02 + 1, 2e-4)
    first = None
    for i0 in range(0, len(t), 2_000_000):
        tt = t[i0:i0 + 2_000_000]
        g = np.abs(np.exp(1j * np.outer(tt, lp)).sum(axis=1))
        idx = np.nonzero(g >= (1 - eta) * M)[0]
        if len(idx): first = tt[idx[0]]; break
    print(f"L={L} M={M} eta={eta}: resscan tau*={ts:.5f}  brute first={first:.5f}  diff={abs(first-ts):.2e}")
