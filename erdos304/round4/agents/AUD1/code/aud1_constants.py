#!/usr/bin/env python3
"""
AUD1: independent checks of the constants / ranges in the CMM fragment.
(1) Lemma CMM:lem-N1 (worst case omega = floor(sqrt L/log L) primes removed from (sqrt L, L/2]).
(2) exponents e(k,v) of Lemma CMM:lem-local.
(3) R', c_*, beta_L of Cor CMM:cor-large (Remark rem-large-num), theta_A of Remark rem-size.
(4) sigma <= 4.5, 2^{-1.596}, zeta(1.3), 4 sqrt3 * 1.852 (Cor T3), 0.3138.
(5) method barrier (Prop CMM:prop-barrier): smallest x with min_k Phi_k >= 1, vs sqrt(L)/log L.
(6) Prop CMM:prop-badexist: explicit bad quadratic character at L=1000 via F_2 linear algebra,
    and the size of |E chi(c')| for it (small primes included).
Usage: nice -n 10 python3 aud1_constants.py > ../out/aud1_constants.txt
"""
import math
import numpy as np
from sympy import primerange, primepi, legendre_symbol
import mpmath as mp

def sieve(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return s

print("# AUD1 constants audit")
# (1) Lemma N1
Nmax = 200000
s = sieve(Nmax); pi = np.cumsum(s)
fails = []; worst = (1e9, None)
for L in range(34, Nmax + 1):
    rt = math.isqrt(L)
    if rt * rt == L: pisq = pi[rt]      # primes <= sqrt L
    else: pisq = pi[rt]
    w = math.floor(math.sqrt(L) / math.log(L))
    N1 = pi[L // 2] - pisq - w
    ratio = N1 / (L / (3 * math.log(L)))
    if L >= 444:
        if ratio < 1: fails.append(L)
        if ratio < worst[0]: worst = (ratio, L)
last_fail_below = max([L for L in range(34, 444) if (pi[L // 2] - pi[math.isqrt(L)] - math.floor(math.sqrt(L) / math.log(L))) < L / (3 * math.log(L))], default=None)
print(f"(1) Lemma N1: L in [444,{Nmax}]: failures={len(fails)}; min ratio N1/(L/(3logL)) = {worst[0]:.4f} at L={worst[1]}; largest failing L below 444: {last_fail_below}")

# (2) e(k,v)
s0 = 2 / math.log(2)
mx = (-1e9, None)
rows = []
for v in range(1, 9):
    row = []
    for k in range(1, v + 1):
        e = (k + 1) / v - s0 * math.log((v + 1) / (v + 1 - k))
        row.append(e)
        if (k, v) != (1, 1) and e > mx[0]: mx = (e, (k, v))
    rows.append("v=%d: " % v + " ".join("%+.4f" % x for x in row))
print("(2) e(k,v) at sigma0=2/log2:"); [print("    " + r) for r in rows]
print(f"    max over (k,v)!=(1,1): {mx[0]:.5f} at {mx[1]}")

# (3) constants
def kstar(L, eta): return 3 * math.log(L) / (2 * (1 - eta) ** 2)
def Rmin(c, kap):
    r = 1
    while math.exp(r) < c * r * kap: r += 1
    return r
for L10 in (12, 16):
    L = 10.0 ** L10; eta = 0.1; ks = kstar(L, eta)
    Rp = Rmin(2, ks); cst = (2 * math.factorial(Rp)) ** (1 / Rp)
    etaL = math.sqrt(L) * math.exp(-eta * math.sqrt(L) / 12)
    for w in (2, 10):
        bL = max(cst * ks * L ** -0.25, math.e * math.sqrt(w * ks) * (L / 2) ** -0.25) + etaL
        print(f"(3) L=1e{L10} eta=0.1 w={w}: kappa*={ks:.2f} (={ks/math.log(L):.3f} logL) R'={Rp} c*={cst:.3f} beta_L={bL:.4f}")
for L10 in (9, 12, 16, 20, 30):
    L = 10.0 ** L10; A = 16; eta = 0.1; ks = kstar(L, eta); RL = Rmin(4, ks)
    th = math.log(2 * RL * ks) / math.log(L / 2) + math.log(4 * RL * ks) / (A * math.log(math.log(L)))
    bnd = math.ceil(2 * math.log(4 * ks) + 2)
    print(f"(3) theta_A: L=1e{L10}: R_L={RL} (<= ceil(2log(4k*)+2)={bnd}) theta={th:.4f}")

# (4) misc numbers
smax = max((math.ceil(3 * math.log2(L)) / math.log(L)) for L in range(444, 200000))
print(f"(4) max sigma (delta=1) over 444<=L<2e5: {smax:.4f}; asymptotic bound 3/log2+1/log444={3/math.log(2)+1/math.log(444):.4f}")
print(f"    0.9*2/log2 - 1 = {1.8/math.log(2)-1:.5f}; 2^-1.596={2**-1.596:.5f}; 1/(1-0.331)={1/(1-0.331):.4f}")
print(f"    zeta(1.3)={float(mp.zeta(1.3)):.5f}; 1.5(zeta(1.3)-1)={1.5*(float(mp.zeta(1.3))-1):.4f}")
print(f"    4*sqrt3*1.852={4*math.sqrt(3)*1.852:.3f}; 1.25506/4={1.25506/4:.5f}; 3/(2*0.81)={3/(2*0.81):.4f}")
# range of c in Cor T3: h' kappa* <= sqrt(L/3)/2 with kappa*=1.852 logL -> h' <= c sqrt(L)/logL with c<=
print(f"    Cor T3 hypothesis allows c <= 1/(2 sqrt3 *1.852) = {1/(2*math.sqrt(3)*1.852):.4f}; nontrivial lower bound needs c < 1/12.83 = {1/12.83:.4f}")

# (5) barrier
def barrier(L):
    N1 = int(primepi(L // 2) - primepi(math.isqrt(L)))
    kap = L / (2 * N1)          # eta -> 0 (smallest kappa)
    lg = math.log(L / 2)
    def logPhi(x):
        best = 1e300
        for k in range(1, int(x) + 50):
            v = math.lgamma(k + 1) + k * math.log(kap) + float(np.logaddexp(-x * lg / 2, x * lg / 2 - k * lg))
            best = min(best, v)
        return best
    x = 1.0
    while logPhi(x) < 0: x += 1 if x < 50 else max(1, int(x * 0.01))
    return N1, kap, x
for L in (10 ** 6, 10 ** 8, 10 ** 10):
    N1, kap, x = barrier(L)
    print(f"(5) barrier L=1e{round(math.log10(L))}: N1={N1} kappa_min={kap:.2f} first integer x with min_k Phi_k>=1: {x:.0f};"
          f" sqrt(L)/logL={math.sqrt(L)/math.log(L):.1f}; ratio={x/(math.sqrt(L)/math.log(L)):.2f}")

# (6) bad quadratic characters at L = 1000
L = 1000
big = [p for p in primerange(2, L // 2 + 1) if p * p > L]
w = len(big) // 2 + 1          # so that w > N1 = len(big) - w
qs = big[:w]; Pp = big[w:]
print(f"(6) L={L}: #primes in (sqrtL,L/2]={len(big)}, omega={w}, N1={len(Pp)}")
Mx = np.array([[0 if legendre_symbol(p, qj) == 1 else 1 for qj in qs] for p in Pp], dtype=np.uint8)
# kernel over F2 by Gaussian elimination
A = Mx.copy(); rows, cols = A.shape; piv = []; r = 0
for c in range(cols):
    pr = next((i for i in range(r, rows) if A[i, c]), None)
    if pr is None: continue
    A[[r, pr]] = A[[pr, r]]
    for i in range(rows):
        if i != r and A[i, c]: A[i] ^= A[r]
    piv.append(c); r += 1
    if r == rows: break
free = [c for c in range(cols) if c not in piv]
f = free[0]; eps = np.zeros(cols, dtype=np.uint8); eps[f] = 1
for i, c in enumerate(piv):
    if A[i, f]: eps[c] = 1
assert not ((Mx.astype(int) @ eps.astype(int)) % 2).any()
S = [qs[j] for j in range(cols) if eps[j]]
chi = lambda n: int(np.prod([legendre_symbol(n % qj, qj) for qj in S]))
assert all(chi(p) == 1 for p in Pp)
print(f"    kernel dim >= {len(free)}; found S of size {len(S)} with chi(p)=1 for all {len(Pp)} p in P' (Re A = N1)")
# |E chi(c')|, c' over all p | Q not in q
Echi = 1.0; zero_by = None
for p in primerange(2, L // 2 + 1):
    if p in qs: continue
    v = 0; pp = p
    while pp <= L: v += 1; pp *= p
    x = chi(p); m = sum(x ** e for e in range(v + 1)) / (v + 1)
    if m == 0 and zero_by is None: zero_by = p
    Echi *= m
print(f"    |E chi(c')| for this 'bad' chi = {abs(Echi):.3e} (first small prime killing it: {zero_by});"
      f" its contribution to B(S) is <= sqrt(q_S)/phi(q_S) ~ q_S^(-1/2) = 10^{-0.5*sum(math.log10(x) for x in S):.1f}")
