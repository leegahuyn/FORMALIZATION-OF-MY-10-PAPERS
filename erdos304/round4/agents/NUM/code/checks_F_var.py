#!/usr/bin/env python3
"""DESIGN S4(ii),(iii) small checks.
(iii) F(t) = (2 - 2^{-it})/(1+it),  |F(t)|^2 = (5 - 4 cos(t log 2))/(1+t^2).
      sup_{|t|>=1} |F(t)|: |F| is even in t.  For t >= 2.87, |F| <= 3/sqrt(1+t^2) < 0.99, so only
      [1, 2.87] matters; there we use a grid of step 1e-6 plus the Lipschitz bound
      |d/dt |F|^2| <= 4 log2/(1+t^2) + 9*2t/(1+t^2)^2 <= 2 log 2 + 4.5 < 6  (t>=1),
      so sup <= max_grid |F|^2 + 6*0.5e-6.
(ii)  u_p = log L - log p over P=(L/2,L]: mean, variance; PNT-limit density 2e^{-u} on [0,log 2):
      E u = 1 - log 2, Var u = 2 - 2log2 - log^2 2 - (1-log2)^2.
      Also checks the pair inequality 1 - |f(t)|^2/M^2 >= (4/pi^2) t^2 Var(u) on 0 < t <= 1
      (valid since |t(u-u')| < pi there), and the finite-L quantities |f(1)|/M and
      max_{1<=t<=10} |f(t)|/M  (so NR(P,T,eta) with lower cut-off |t|>=1 needs eta <= 1 - that max).
output: stdout (saved to out/checks_F_var.txt) and data/var_u.csv"""
import numpy as np, math, csv, os
from sympy import primerange
here = os.path.dirname(os.path.abspath(__file__))
l2 = math.log(2)
# (iii)
t = np.arange(1.0, 2.87 + 1e-6, 1e-6)
F2 = (5 - 4 * np.cos(t * l2)) / (1 + t * t)
i = int(np.argmax(F2))
sup_grid = math.sqrt(F2[i]); sup_bound = math.sqrt(F2[i] + 6 * 0.5e-6)
print(f"(iii) max_(1<=t<=2.87) |F(t)| on grid: {sup_grid:.8f} at t={t[i]:.6f}; certified sup <= {sup_bound:.8f}")
print(f"      |F(1)| = {math.sqrt((5-4*math.cos(l2))/2):.8f}; tail bound 3/sqrt(1+2.87^2) = {3/math.sqrt(1+2.87**2):.6f}")
for thr in (0.9, 0.8, 0.7):
    tt = np.arange(1.0, 20, 1e-5); FF = np.sqrt((5 - 4*np.cos(tt*l2))/(1+tt*tt))
    last = tt[np.nonzero(FF >= thr)[0][-1]]
    print(f"      last t>=1 with |F(t)| >= {thr}: t = {last:.4f}")
# (ii)
Eu = 1 - l2; Vu = 2 - 2*l2 - l2**2 - Eu**2
print(f"(ii) PNT limit: E u = {Eu:.6f}, Var u = {Vu:.6f}, sd = {math.sqrt(Vu):.6f}")
rows = []
for L in [31, 61, 100, 173, 251, 353, 1000, 10**4, 10**5, 10**6, 10**7]:
    ps = np.array(list(primerange(L // 2 + 1, L + 1)), dtype=float)
    M = len(ps); u = math.log(L) - np.log(ps)
    var = float(u.var())
    lp = np.log(ps)
    # pair inequality on 0<t<=1 and finite-L |f|/M on [1,10]
    if M <= 5000:
        ts = np.linspace(1e-3, 1.0, 2000)
        f = np.abs(np.exp(1j * np.outer(ts, lp - lp.mean())).sum(axis=1)) / M
        lhs = 1 - f**2; rhs = (4 / math.pi**2) * ts**2 * var
        pair_ok = bool(np.all(lhs >= rhs - 1e-12)); ratio = float(np.min(lhs / rhs))
        t2 = np.arange(1.0, 10.0, 1e-3)
        g = np.abs(np.exp(1j * np.outer(t2, lp - lp.mean())).sum(axis=1)) / M
        f1 = float(g[0]); gmax = float(g.max()); tmax = float(t2[int(np.argmax(g))])
    else:
        pair_ok = ''; ratio = float('nan')
        # chunked evaluation for large pools
        def gm(tvals):
            out = []
            for tv in tvals:
                out.append(abs(np.exp(1j * tv * (lp - lp.mean())).sum()) / M)
            return np.array(out)
        t2 = np.arange(1.0, 10.0, 1e-2); g = gm(t2)
        f1 = float(g[0]); gmax = float(g.max()); tmax = float(t2[int(np.argmax(g))])
    Ft1 = math.sqrt((5 - 4*math.cos(l2))/2)
    rows.append(dict(L=L, M=M, mean_u=float(u.mean()), var_u=var, pair_ineq_ok=pair_ok,
                     min_ratio_lhs_rhs=ratio, f1_over_M=f1, max_1_10_over_M=gmax, argmax_t=tmax))
    print(f"   L={L:>8d} M={M:>6d} mean u={u.mean():.5f} Var u={var:.5f}  pair ineq on (0,1]: {pair_ok} "
          f"(min lhs/rhs={ratio:.3f})  |f(1)|/M={f1:.5f} (|F(1)|={Ft1:.5f})  max_[1,10]|f|/M={gmax:.5f} at t={tmax:.3f}")
with open(os.path.join(here, '..', 'data', 'var_u.csv'), 'w', newline='') as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
