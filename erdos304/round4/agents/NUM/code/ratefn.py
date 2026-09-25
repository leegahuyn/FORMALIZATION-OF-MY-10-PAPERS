#!/usr/bin/env python3
"""Random-phase model constants for the resonance experiment (HEURISTIC comparison only).
I(x) = sup_l (l x - log I_0(l)): Cramer rate for |(1/M) sum e^{i theta_p}| >= x, theta_p iid uniform
(log-MGF of the 2D vector (cos,sin) is log I_0(|l|), radially symmetric).
Dirichlet exponent: with Q = pi*sqrt(2/eta) boxes, a q <= Q^{M-1} aligns M-1 relative phases within
2pi/Q, giving |f| >= M cos(2pi/Q)... we just print log Q (the per-prime exponent)."""
import mpmath as mp
for eta in (0.3, 0.2, 0.1, 0.05):
    x = 1 - eta
    lam = mp.findroot(lambda l: mp.besseli(1, l) / mp.besseli(0, l) - x, 3)
    I = lam * x - mp.log(mp.besseli(0, lam))
    Q = mp.pi * mp.sqrt(2 / eta)
    print(f"eta={eta}: x={x} lambda*={float(lam):.5f} I(x)={float(I):.5f} (per M, natural log) = {float(I/mp.log(10)):.5f} decimal digits per prime;  Dirichlet log10 Q = {float(mp.log10(Q)):.4f}")
