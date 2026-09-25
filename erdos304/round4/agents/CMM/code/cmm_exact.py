#!/usr/bin/env python3
"""
CMM numerics (agent CMM, Erdos-Graham #304 round 4).

Exact computation of mu_i(b/q) = E e(b X_i / q) for the independent-uniform-exponent
window model of p1p4 Def 4.4:
    X = c * U(E),  c = prod_{p | Q} p^{e_p}, e_p uniform on {0..v_p(Q)} independent,
    E = uniform t-subset of a sub-pool P_i of P = (L/2, L] primes.
The law of X mod q is computed EXACTLY by dynamic programming on Z/q (multiplicative
convolution), then mu(b/q) for all b is obtained by one FFT.  This is independent of the
character expansion used in the proof.

Compared with the main term
    M(q) = prod_j (v_j + 1 - k_j - 1/(p_j - 1)) / (v_j + 1)     (q = prod p_j^{k_j})
(for squarefree q with p_j in (sqrt L, L/2] this is prod_j (1/2 - 1/(2(p_j-1)))).

Also computes, for squarefree q, the exact quantities B(S) of the proof
    B(S) = prod_{j in S} sqrt(q_j)/(q_j-1) * sum_{chi primitive mod q_S} |E chi(c')|
and the resulting rigorous error bound  sum_{S != 0} B(S) prod_{j in S}(1-pi_j) prod_{j notin S} rho0_j,
the number of 'bad' primitive characters (Re A(chi) > N1/2), and the moment-method bound.

Usage: nice -n 10 python3 cmm_exact.py  (writes ../out/cmm_exact.txt)
"""
import itertools, math, sys, time
import numpy as np
from sympy import primerange, primitive_root, isprime, factorint

def vQ(p, L):
    v = 0; pp = p
    while pp <= L:
        v += 1; pp *= p
    return v

def pool(L):
    return [p for p in primerange(L // 2 + 1, L + 1)]

def mult_perm(dist, m, q):
    """law of (m*x mod q) given law 'dist' of x (m arbitrary integer)."""
    idx = (np.arange(q, dtype=np.int64) * (m % q)) % q
    return np.bincount(idx, weights=dist, minlength=q)

def law_X_mod_q(L, q, Pi, t):
    """exact law of X mod q (vector of length q)."""
    # U = product of uniform t-subset of Pi, mod q
    f = [np.zeros(q) for _ in range(t + 1)]
    f[0][1 % q] = 1.0
    for p in Pi:
        for c in range(t, 0, -1):
            f[c] = f[c] + mult_perm(f[c - 1], p, q)
    dist = f[t] / f[t].sum()
    # multiply by p^{e_p}, e_p uniform on {0..v_p}, for every p | Q (p <= L/2)
    for p in primerange(2, L // 2 + 1):
        v = vQ(p, L)
        acc = np.zeros(q)
        pe = 1
        for e in range(v + 1):
            acc += mult_perm(dist, pe, q)
            pe = (pe * p) % q
        dist = acc / (v + 1)
    return dist

def mu_all(dist):
    q = len(dist)
    # mu(b/q) = sum_x P(x) e(bx/q) = q * ifft(P)[b]
    return np.fft.ifft(dist) * q

def main_term(L, q):
    M = 1.0
    for p, k in factorint(q).items():
        v = vQ(p, L)
        assert k <= v, "q must divide Q"
        M *= (v + 1 - k - 1.0 / (p - 1)) / (v + 1)
    return M

def units_mask(q):
    b = np.arange(q)
    return np.gcd(b, q) == 1

# ---------- character side (squarefree q) ----------
def dlog_table(r):
    g = primitive_root(r)
    ind = np.zeros(r, dtype=np.int64); x = 1
    for k in range(r - 1):
        ind[x] = k; x = (x * g) % r
    return ind

def Echi_cprime_prim(L, qs, excl):
    """array over primitive characters chi mod prod(qs) of E chi(c'),
    c' = prod_{p | Q, p not in excl} p^{e_p}. Characters indexed by (k_1..k_r), k_j in 1..q_j-2."""
    inds = [dlog_table(r) for r in qs]
    shape = tuple(r - 2 for r in qs)
    ks = [np.arange(1, r - 1) for r in qs]
    E = np.ones(shape, dtype=complex)
    for p in primerange(2, L // 2 + 1):
        if p in excl:
            continue
        v = vQ(p, L)
        # phase of chi(p) = sum_j k_j ind_j(p)/(q_j-1)
        ph = np.zeros(shape)
        for j, r in enumerate(qs):
            a = (ks[j] * inds[j][p % r]) / (r - 1)
            sh = [1] * len(qs); sh[j] = r - 2
            ph = ph + a.reshape(sh)
        z = np.exp(2j * np.pi * ph)
        # E z^{e}, e uniform 0..v
        s = np.zeros(shape, dtype=complex); zp = np.ones(shape, dtype=complex)
        for e in range(v + 1):
            s += zp; zp = zp * z
        E *= s / (v + 1)
    return E

def A_prim(L, qs, excl):
    """A(chi) = sum_{p in P'} chi(p) over primitive chi mod prod(qs); P' = (sqrt L, L/2] primes minus excl."""
    inds = [dlog_table(r) for r in qs]
    shape = tuple(r - 2 for r in qs)
    ks = [np.arange(1, r - 1) for r in qs]
    A = np.zeros(shape, dtype=complex); N1 = 0
    for p in primerange(2, L // 2 + 1):
        if p * p <= L or p in excl:
            continue
        N1 += 1
        ph = np.zeros(shape)
        for j, r in enumerate(qs):
            a = (ks[j] * inds[j][p % r]) / (r - 1)
            sh = [1] * len(qs); sh[j] = r - 2
            ph = ph + a.reshape(sh)
        A += np.exp(2j * np.pi * ph)
    return A, N1

def check_gauss_expansion(qp, trials=5, rng=None):
    """verify e(b y/q') = (1/phi(q')) sum_chi conj(chi)(b y) tau(chi) for squarefree q' (numerically)."""
    rng = rng or np.random.default_rng(1)
    fac = list(factorint(qp).keys())
    inds = [dlog_table(r) for r in fac]
    phi = int(np.prod([r - 1 for r in fac]))
    worst = 0.0
    # tau(chi) = sum_{x unit mod q'} chi(x) e(x/q')
    xs = np.array([x for x in range(qp) if math.gcd(x, qp) == 1])
    for _ in range(trials):
        b = int(rng.integers(1, qp));
        while math.gcd(b, qp) != 1: b = int(rng.integers(1, qp))
        y = int(rng.integers(1, qp));
        while math.gcd(y, qp) != 1: y = int(rng.integers(1, qp))
        tot = 0j
        for ks in itertools.product(*[range(r - 1) for r in fac]):
            def chi(x):
                return np.exp(2j * np.pi * sum(k * inds[j][x % r] / (r - 1) for j, (k, r) in enumerate(zip(ks, fac))))
            tau = np.sum(chi(xs) * np.exp(2j * np.pi * xs / qp))
            tot += np.conj(chi(b * y % qp)) * tau
        tot /= phi
        worst = max(worst, abs(tot - np.exp(2j * np.pi * b * y / qp)))
    return worst

def run_case(L, qfac, Pi, t, out, do_B=True):
    q = int(np.prod(qfac))
    t0 = time.time()
    dist = law_X_mod_q(L, q, Pi, t)
    mu = mu_all(dist)
    U = units_mask(q)
    M = main_term(L, q)
    err = np.abs(mu[U] - M)
    emax = err.max()
    omega = len(qfac)
    sqf = all(v == 1 for v in factorint(q).values())
    line = (f"L={L:5d} q={'*'.join(map(str,qfac)):>16s}={q:<9d} |Pi|={len(Pi):3d} t={t} "
            f"M(q)={M:.10f} 2^w*M={M*2**omega:.8f} max|mu-M|={emax:.3e} "
            f"(2^w*max|mu-M|={emax*2**omega:.3e})")
    extra = ""
    if do_B and sqf and all(r >= 3 for r in qfac) and q <= 4_000_000:
        # rigorous-bound chain with exact B(S)
        excl = set(qfac)
        pis = [vQ(r, L) / (vQ(r, L) + 1) for r in qfac]
        rho0 = [pis[j] + (1 - pis[j]) / (qfac[j] - 1) for j in range(omega)]
        bound = 0.0; Bmax = {}
        nbad_tot = 0
        for rS in range(1, omega + 1):
            for S in itertools.combinations(range(omega), rS):
                qs = [qfac[j] for j in S]
                E = Echi_cprime_prim(L, qs, excl)
                BS = np.prod([math.sqrt(r) / (r - 1) for r in qs]) * np.abs(E).sum()
                Bmax[S] = BS
                A, N1 = A_prim(L, qs, excl)
                nbad = int((A.real > N1 / 2).sum())
                nbad_tot += nbad
                w = np.prod([1 - pis[j] for j in S]) * np.prod([rho0[j] for j in range(omega) if j not in S])
                bound += BS * w
        extra = (f"\n      exact-B bound on max|mu-M| = {bound:.3e} (ratio true/bound = {emax/bound if bound>0 else float('nan'):.3e});"
                 f" B(S): " + ", ".join(f"{tuple(qfac[j] for j in S)}:{b:.2e}" for S, b in Bmax.items()) +
                 f"; #bad prim chars (Re A>N1/2) over all S = {nbad_tot}")
    line += extra + f"   [{time.time()-t0:.1f}s]"
    print(line); out.write(line + "\n"); out.flush()
    return emax, M

if __name__ == "__main__":
    outpath = sys.argv[1] if len(sys.argv) > 1 else "../out/cmm_exact.txt"
    with open(outpath, "w") as out:
        out.write("# CMM exact numerics: mu_i(b/q) vs main term M(q); see cmm_exact.py docstring\n")
        # 0) Gauss-sum expansion check (with conjugate)
        for qp in [15, 21, 35, 105, 143]:
            w = check_gauss_expansion(qp)
            s = f"Gauss expansion e(by/q')=(1/phi) sum conj(chi)(by) tau(chi): q'={qp}, max err={w:.2e}"
            print(s); out.write(s + "\n")
        # 1) squarefree, primes in (sqrt L, L/2], omega = 2, 3
        cases = []
        for L in [60, 100, 200, 300]:
            P = pool(L)
            big = [p for p in primerange(2, L // 2 + 1) if p * p > L]
            # omega=2: two largest, two smallest large primes
            cases.append((L, [big[-1], big[-2]], P[:4], 2))
            cases.append((L, [big[0], big[1]], P[:4], 2))
            cases.append((L, [big[0], big[-1]], P, max(1, len(P) // 2)))
            if L <= 300:
                trip = [big[0], big[1], big[2]]
                if np.prod(trip) <= 3_500_000:
                    cases.append((L, trip, P[:3], 1))
        for L in [1000, 2000]:
            P = pool(L)
            big = [p for p in primerange(2, L // 2 + 1) if p * p > L]
            cases.append((L, [big[-1], big[-2]], P[:3], 2))
            cases.append((L, [big[0], big[1]], P[:3], 2))
            cases.append((L, [big[0], big[1], big[2]], P[:2], 1))
        # 2) small primes (v >= 2) and prime powers: general main term
        for L in [60, 100, 300]:
            P = pool(L)
            cases.append((L, [3, 5], P[:3], 2))
            cases.append((L, [3, 7, 11], P[:3], 2))
            cases.append((L, [9, 5], P[:3], 2))
            cases.append((L, [4, 7], P[:3], 2))
            cases.append((L, [8, 9, 5], P[:3], 1))
        for (L, qfac, Pi, t) in cases:
            run_case(L, qfac, Pi, t, out)
