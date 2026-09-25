#!/usr/bin/env python3
"""
AUD1: independent check of Lemma CMM:lem-local with exact F_p = sum_k p^k rho_{p^k}^{s0},
rho_{p^k} = (v+1-k+Gamma)/(v+1), constant Gamma.
(i)  p <= L^{1/9}:  F_p <= 1.5 p^{1+sigma Gamma - 0.9 sigma}  (tested for several Gamma, incl. Gamma > 1)
(ii) sum_{L^{1/9}<p<=L/2} F_p <= 36 L^{-c1/2} when sigma*Gamma = c1/2 (extreme allowed value).
Usage: nice -n 10 python3 aud1_local.py > ../out/aud1_local.txt
"""
import math
import numpy as np

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]

def vQ(p, L):
    v, pp = 0, p
    while pp <= L: v += 1; pp *= p
    return v

print("# AUD1 check of Lemma CMM:lem-local")
for L in (10 ** 5, 10 ** 6, 10 ** 7, 10 ** 8):
    P = primes_upto(L // 2)
    for delta in (0.05, 0.3, 1.0):
        s0 = math.ceil((2 + delta) * math.log2(L)); sig = s0 / math.log(L)
        c1 = min(delta, 0.089)
        # (i)
        worst_i = 0.0
        for G in (0.0, 0.3, 1.0, 2.5):
            for p in P[P <= L ** (1 / 9)]:
                p = int(p); v = vQ(p, L)
                F = sum(math.exp(k * math.log(p) + s0 * math.log((v + 1 - k + G) / (v + 1))) for k in range(1, v + 1))
                bnd = 1.5 * p ** (1 + sig * G - 0.9 * sig)
                worst_i = max(worst_i, F / bnd)
        # (ii) with sigma*Gamma = c1/2
        G = c1 / (2 * sig)
        tot = 0.0
        for p in P[P > L ** (1 / 9)]:
            p = int(p); v = vQ(p, L)
            tot += sum(math.exp(k * math.log(p) + s0 * math.log((v + 1 - k + G) / (v + 1))) for k in range(1, v + 1))
        print(f"L=1e{round(math.log10(L))} delta={delta}: sigma={sig:.3f}  (i) max F_p/bound={worst_i:.4f}  (ii) sum/(36L^(-c1/2))={tot/(36*L**(-c1/2)):.3e}")
