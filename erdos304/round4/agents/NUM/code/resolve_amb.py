#!/usr/bin/env python3
"""Resolve AMBIGUOUS candidates reported by resscan (fine grid max within the Lipschitz slack
just below (1-eta)M): locate the local maximum of g(t)=|sum_{p in P} p^{it}| near t0 exactly
(mpmath, 50 digits; root of d/dt |f|^2 = 2 Re(conj(f) f')), and decide g_max >= (1-eta)M or not.
usage: resolve_amb.py L eta t0 [halfwidth]"""
import sys
import mpmath as mp
from sympy import primerange
mp.mp.dps = 50
L = int(sys.argv[1]); eta = mp.mpf(sys.argv[2]); t0 = mp.mpf(sys.argv[3])
hw = mp.mpf(sys.argv[4]) if len(sys.argv) > 4 else mp.mpf('0.2')
ps = list(primerange(L // 2 + 1, L + 1)); M = len(ps)
lp = [mp.log(p) for p in ps]
def f(t): return mp.fsum(mp.expj(t * l) for l in lp)
def fp(t): return mp.fsum(1j * l * mp.expj(t * l) for l in lp)
def dg2(t): return 2 * mp.re(mp.conj(f(t)) * fp(t))
# coarse scan for the best start
best = None
N = 400
for i in range(N + 1):
    t = t0 - hw + 2 * hw * i / N
    g = abs(f(t))
    if best is None or g > best[1]: best = (t, g)
tm = mp.findroot(dg2, best[0])
gm = abs(f(tm))
print(f"L={L} M={M} eta={eta}: local max of g at t={mp.nstr(tm, 20)}: g/M={mp.nstr(gm / M, 12)}  "
      f"threshold {1 - eta}: {'RESONANCE (g>=thr)' if gm >= (1 - eta) * M else 'no resonance (g<thr)'}")
# first crossing of g = (1-eta)M to the left of the local maximum (bisection on [t0-hw, tm])
a, b = t0 - hw, tm
if abs(f(a)) < (1 - eta) * M <= gm:
    for _ in range(80):
        c = (a + b) / 2
        if abs(f(c)) >= (1 - eta) * M: b = c
        else: a = c
    # certify no crossing on [t0-hw, a] with a Lipschitz grid (K = sum |log p - c_L|)
    cL = mp.log(L) - mp.log(2) / 2; K = mp.fsum(abs(l - cL) for l in lp)
    h = mp.mpf('4e-6'); t = t0 - mp.mpf('0.1027'); ok = True; n = 0
    while t < a - mp.mpf('1e-3'):
        if abs(f(t)) >= (1 - eta) * M - K * h / 2: ok = False; break
        t += h; n += 1
    print(f"   first crossing t_c = {mp.nstr(b, 15)};  certified no resonance on [{mp.nstr(t0 - mp.mpf('0.1027'), 12)} (= left end of the ambiguous resscan cell), t_c - 1e-3]: {ok} ({n} grid points, step 4e-6)")
