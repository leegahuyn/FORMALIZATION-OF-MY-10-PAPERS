#!/usr/bin/env python3
"""Sanity check of Lemma CMM:local (i),(ii) (agent CMM): exact F_p vs the bounds, random Gamma_p."""
import math, random
from sympy import primerange
random.seed(3)
worst_i = 0.0; worst_ii = -1e9
for L in [10**4, 10**6, 10**8, 10**10]:
    lL = math.log(L)
    for delta in [0.05, 0.3, 1.0]:
        s0 = math.ceil((2+delta)*lL/math.log(2)); sig = s0/lL
        c1 = min(delta, 0.089)
        # (i)
        for p in list(primerange(2, min(int(L**(1/9))+1, 2000))):
            v = int(math.floor(math.log(L)/math.log(p)+1e-12))
            while p**(v+1) <= L: v += 1
            while p**v > L: v -= 1
            for G in [0, 0.01, 0.1, 0.5, 1.0, 3.0]:
                F = sum(p**k * ((v+1-k+G)/(v+1))**s0 for k in range(1, v+1))
                B = 1.5*p**(1+sig*G-0.9*sig)
                worst_i = max(worst_i, F/B)
        # (ii): Gamma* = c1/(2 sigma), sum over p in (L^{1/9}, L/2] via exponent bound per (k,v)
        G = c1/(2*sig)
        tot = 0.0
        if L <= 10**8:
            for p in primerange(int(L**(1/9))+1, L//2+1):
                v = 1
                while p**(v+1) <= L: v += 1
                tot += sum(p**k*((v+1-k+G)/(v+1))**s0 for k in range(1, v+1))
            worst_ii = max(worst_ii, tot/(36*L**(-c1/2)))
print(f"(i): max F_p / bound = {worst_i:.4f} (must be <= 1)")
print(f"(ii): max sum / (36 L^(-c1/2)) = {worst_ii:.4e} (must be <= 1)")
