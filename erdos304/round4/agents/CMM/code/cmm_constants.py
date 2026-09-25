#!/usr/bin/env python3
"""
CMM constants and finite checks (agent CMM).
 (1) exponents e(k,v) = (k+1)/v - sigma0*log((v+1)/(v+1-k)), sigma0 = 2/log 2, 1<=k<=v<=8
     (used in Lemma CMM:local (ii)); exact margin c0.
 (2) direct check of N1 >= L/(3 log L) for 444 <= L <= 200000 with omega = floor(sqrt L/log L)
     (sanity check of Lemma CMM:N1, whose proof uses Rosser-Schoenfeld).
 (3) the explicit quantities of Thm CMM:main / Cor CMM:large:
     kappa_* = 3 log L/(2(1-eta)^2), R_L, theta_A(L), beta_L(omega), eps_L(omega);
     and the relative error bound of Thm CMM:asym.
 (4) the conjugation check: e(by/q) = (1/phi) sum_chi conj(chi(by)) tau(chi) holds, while the
     version without conjugate fails.
Usage: python3 cmm_constants.py > ../out/cmm_constants.txt
"""
import math, itertools
import numpy as np
from sympy import primepi, primitive_root

sigma0 = 2 / math.log(2)
print("(1) exponents e(k,v) for sigma0 = 2/log 2 =", sigma0)
worst = -1e9; worst_kv = None
for v in range(1, 9):
    row = []
    for k in range(1, v + 1):
        e = (k + 1) / v - sigma0 * math.log((v + 1) / (v + 1 - k))
        row.append(f"{e:+.4f}")
        if (k, v) != (1, 1) and e > worst:
            worst, worst_kv = e, (k, v)
    print(f"  v={v}: " + " ".join(row))
print(f"  max over (k,v) != (1,1): {worst:.5f} at {worst_kv}  => c0 = {-worst:.5f}")

print("\n(2) N1 >= L/(3 log L) check, omega = floor(sqrt(L)/log L):")
bad = []
Ls = list(range(444, 5000)) + list(range(5000, 200001, 97))
for L in Ls:
    om = int(math.sqrt(L) / math.log(L))
    N1 = int(primepi(L // 2)) - int(primepi(int(math.isqrt(L)))) - om
    if N1 < L / (3 * math.log(L)):
        bad.append(L)
print(f"  checked {len(Ls)} values of L in [444, 200000]; failures: {bad[:10]} (count {len(bad)})")
# asymptotic kappa = 2L/N1 / log L
for L in [10**3, 10**4, 10**5, 10**6, 10**7]:
    N1 = int(primepi(L // 2)) - int(primepi(int(math.isqrt(L))))
    print(f"  L={L:>9d}: N1={N1}, 2L/N1 = {2*L/N1:.3f} = {2*L/N1/math.log(L):.3f} log L,  L/(2N1) = {L/(2*N1)/math.log(L):.3f} log L")

def consts(L, A, eta, omega):
    lL = math.log(L)
    ks = 3 * lL / (2 * (1 - eta) ** 2)              # kappa_*
    R = 1
    while math.exp(R) < 4 * R * ks:
        R += 1
    Z = lL ** A
    lam = math.log(2 * omega * ks) / math.log(L / 2)
    theta = math.log(2 * R * ks) / math.log(L / 2) + math.log(4 * R * ks) / math.log(Z)
    etaL = math.sqrt(L) * math.exp(-eta * math.sqrt(L) / 12)
    # Cor CMM:large: beta_L(omega) = e (2 omega k*)^{1/2} (L/2)^{-1/4} + (L/2)^{theta/2-1/4} + eta_L
    betaL = math.e * math.sqrt(2 * omega * ks) * (L / 2) ** (-0.25) + (L / 2) ** (theta / 2 - 0.25) + etaL
    epsL = 0.5 * (1 / (math.sqrt(L) - 1) + betaL)
    return ks, R, lam, theta, etaL, betaL, epsL

print("\n(3) explicit constants (log10 L, A, eta, omega): kappa_*/logL, R_L, lambda, theta_A, eta_L, beta_L, eps_L")
for lg in [6, 9, 12, 16, 20, 30, 50]:
    L = 10.0 ** lg
    for A in [8, 16]:
        for eta in [0.5, 0.1]:
            for omega in [2, 10, 1000]:
                if 2 * omega * 3 * math.log(L) / (2 * (1 - eta) ** 2) > math.sqrt(L / 2):
                    continue
                ks, R, lam, th, etaL, bL, eL = consts(L, A, eta, omega)
                print(f"  10^{lg:<3d} A={A:2d} eta={eta:.1f} w={omega:5d}: k*/logL={ks/math.log(L):.3f} R={R:3d} "
                      f"lam={lam:.4f} theta={th:.4f} etaL={etaL:.2e} beta={bL:.3e} eps={eL:.3e}")

print("\n(3b) relative error bound of Thm CMM:asym, E <= e^{w/(y-1)} (4 w kappa_*/sqrt(y) + eta'_L), y = sqrt(L) and y = L/3, eta=0.1")
for lg in [8, 12, 16, 20, 30]:
    L = 10.0 ** lg; lL = math.log(L); ks = 3 * lL / (2 * 0.81)
    for omega in [2, 3, 10]:
        for (nm, y) in [("sqrtL", math.sqrt(L)), ("L/3", L / 3)]:
            if omega * ks / math.sqrt(y) > 0.5:
                print(f"  10^{lg} w={omega} y={nm}: outside range (w kappa/sqrt y > 1/2)"); continue
            E = math.exp(omega / (y - 1)) * 4 * omega * ks / math.sqrt(y)
            print(f"  10^{lg} w={omega} y={nm}: E <= {E:.3e}")

print("\n(4) conjugation check at q' = 15, 77:")
def dlog(r):
    g = primitive_root(r); ind = {}; x = 1
    for k in range(r - 1):
        ind[x] = k; x = x * g % r
    return ind
for qp, fac in [(15, [3, 5]), (77, [7, 11])]:
    inds = [dlog(r) for r in fac]
    units = [x for x in range(qp) if math.gcd(x, qp) == 1]
    phi = len(units)
    def chi(ks, x):
        return np.exp(2j * np.pi * sum(k * inds[j][x % r] / (r - 1) for j, (k, r) in enumerate(zip(ks, fac))))
    e1 = e2 = 0.0
    for b in units[:4]:
        for y in units[:6]:
            s1 = s2 = 0j
            for ks in itertools.product(*[range(r - 1) for r in fac]):
                tau = sum(chi(ks, x) * np.exp(2j * np.pi * x / qp) for x in units)
                s1 += np.conj(chi(ks, b * y % qp)) * tau
                s2 += chi(ks, b * y % qp) * tau
            t = np.exp(2j * np.pi * b * y / qp)
            e1 = max(e1, abs(s1 / phi - t)); e2 = max(e2, abs(s2 / phi - t))
    print(f"  q'={qp}: with conjugate max err {e1:.2e}; without conjugate max err {e2:.2e}")
