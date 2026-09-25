#!/usr/bin/env python3
"""
AUD1 independent audit numerics for the CMM fragment (Erdos-Graham #304, round 4).
Written from scratch (does not import or copy CMM code).

(1) Exact law of X = c*U mod q in the uniform-exponent window model; U is built by
    enumerating subsets (itertools.combinations) or held FIXED (deterministic U: an
    adversarial choice allowed by 'arbitrary law of E').  mu(b/q) by a direct DFT sum.
(2) Main term M(q) = prod (v+1-k-1/(p-1))/(v+1).
(3) Prop CMM:prop-exact error bound, computed with my own character machinery on
    (Z/d)^x, including 2-power components (Z/2^m)^x = <-1> x <5>.
(4) Lemma good check |E chi(c')| <= exp(-(N1 - Re A)/4) for all primitive chi.
(5) Moment count check (Lemma CMM:lem-moment) : #bad(all chi mod d) <= bound, several k.
(6) Conjugation check of e(by/q') = (1/phi) sum_chi conj(chi)(by) tau(chi).
Usage: nice -n 10 python3 aud1_exact.py > ../out/aud1_exact.txt
"""
import itertools, math, cmath, time
import numpy as np
from sympy import primerange, factorint, primitive_root, isprime

def vQ(p, L):
    v, pp = 0, p
    while pp <= L:
        v += 1; pp *= p
    return v

def qprimes(L):           # primes dividing Q (p <= L/2)
    return list(primerange(2, L // 2 + 1))

def poolp(L):
    return list(primerange(L // 2 + 1, L + 1))

# ---------------- law of c mod n over a given set of primes ----------------
def law_c(L, n, primes):
    dist = np.zeros(n); dist[1 % n] = 1.0
    for p in primes:
        v = vQ(p, L)
        new = np.zeros(n)
        pe = 1
        for e in range(v + 1):
            idx = (np.arange(n) * pe) % n
            np.add.at(new, idx, dist)
            pe = (pe * p) % n
        dist = new / (v + 1)
    return dist

def law_U(n, Pi, t, fixed=False):
    dist = np.zeros(n)
    if fixed:                       # deterministic U = product of first t primes of Pi
        u = 1
        for p in Pi[:t]: u = (u * p) % n
        dist[u] = 1.0; return dist
    cnt = 0
    for E in itertools.combinations(Pi, t):
        u = 1
        for p in E: u = (u * p) % n
        dist[u] += 1; cnt += 1
    return dist / cnt

def mult_conv(d1, d2, n):
    out = np.zeros(n)
    nz = np.nonzero(d2)[0]
    ar = np.arange(n)
    for r in nz:
        np.add.at(out, (ar * r) % n, d1 * d2[r])
    return out

def mu_direct(dist, n, bs):
    r = np.arange(n)
    if n > 4000:   # FFT (numpy ifft has + sign), spot-checked against the direct sum
        full = np.fft.ifft(dist) * n
        for b in bs[:5]:
            assert abs(full[b] - np.sum(dist * np.exp(2j * np.pi * b * r / n))) < 1e-12
        return full[np.array(bs)]
    return np.array([np.sum(dist * np.exp(2j * np.pi * b * r / n)) for b in bs])

def M_of(L, fac):
    M = 1.0
    for p, k in fac.items():
        v = vQ(p, L); M *= (v + 1 - k - 1.0 / (p - 1)) / (v + 1)
    return M

def rho0_of(L, p, k):
    v = vQ(p, L); return (v + 1 - k + 1.0 / (p - 1)) / (v + 1)

# ---------------- characters of (Z/d)^x ----------------
def comp_struct(p, m):
    """cyclic factors of (Z/p^m)^x: list of (generator, order) and primitivity test on index tuple."""
    pm = p ** m
    if p != 2:
        g = primitive_root(pm); o = (p - 1) * p ** (m - 1)
        prim = (lambda t: t % o != 0) if m == 1 else (lambda t: t % p != 0)
        return pm, [(g, o)], lambda ts: prim(ts[0])
    if m == 1:
        return 2, [], lambda ts: False                 # no primitive character mod 2
    if m == 2:
        return 4, [(3, 2)], lambda ts: ts[0] == 1
    return pm, [(pm - 1, 2), (5, 2 ** (m - 2))], lambda ts: ts[1] % 2 == 1

def dlog_comp(p, m):
    """map unit residue mod p^m -> exponent tuple."""
    pm, gens, _ = comp_struct(p, m)
    table = {}
    if not gens:
        table[1] = (); return table
    ranges = [range(o) for (_, o) in gens]
    for ex in itertools.product(*ranges):
        r = 1
        for (g, o), e in zip(gens, ex): r = r * pow(g, e, pm) % pm
        table[r] = ex
    assert len(table) == (pm // p) * (p - 1)
    return table

class CharGroup:
    def __init__(self, fac):          # fac: list of (p, m)
        self.fac = fac
        self.d = 1
        for p, m in fac: self.d *= p ** m
        self.shape, self.primtests, self.tables = [], [], []
        for p, m in fac:
            pm, gens, pt = comp_struct(p, m)
            self.shape.append(tuple(o for (_, o) in gens)); self.primtests.append(pt)
            self.tables.append(dlog_comp(p, m))
        self.fullshape = tuple(o for s in self.shape for o in s)
    def index(self, r):
        ex = []
        for (p, m), tab in zip(self.fac, self.tables):
            ex.extend(tab[r % (p ** m)])
        return tuple(ex)
    def transform(self, dist):
        """dist: array over Z/d (mass on units).  Returns array T[t] = sum_r dist[r] chi_t(r),
        chi_t(r) = exp(2 pi i sum t_i a_i(r)/o_i)."""
        F = np.zeros(self.fullshape if self.fullshape else (1,), dtype=complex)
        for r in range(self.d):
            if dist[r] != 0 and math.gcd(r, self.d) == 1:
                F[self.index(r) if self.fullshape else (0,)] += dist[r]
        if not self.fullshape: return F
        return np.fft.ifftn(F) * F.size    # ifftn has + sign: sum F[a] e(+t.a/o)
    def primitive_mask(self):
        if not self.fullshape: return np.zeros((1,), dtype=bool)
        mask = np.zeros(self.fullshape, dtype=bool)
        for t in itertools.product(*[range(o) for o in self.fullshape]):
            pos, ok = 0, True
            for s, pt in zip(self.shape, self.primtests):
                ts = t[pos:pos + len(s)]; pos += len(s)
                if not pt(ts): ok = False; break
            mask[t] = ok
        return mask

def phi(n):
    r = n
    for p in factorint(n): r = r // p * (p - 1)
    return r

# ---------------- main audit of one case ----------------
def audit_case(L, qfac, npool, t, fixedU=False, eta=0.5, do_bound=True):
    q = 1
    for p, k in qfac.items(): q *= p ** k
    Qp = qprimes(L)
    for p, k in qfac.items(): assert p in Qp and k <= vQ(p, L)
    Pi = poolp(L)[:npool]
    t0 = time.time()
    dc = law_c(L, q, Qp)
    dU = law_U(q, Pi, t, fixed=fixedU)
    dX = mult_conv(dc, dU, q)
    units = [b for b in range(1, q) if math.gcd(b, q) == 1]
    mus = mu_direct(dX, q, units)
    M = M_of(L, qfac)
    err = np.max(np.abs(mus - M))
    w = len(qfac)
    line = (f"L={L:5d} q={'*'.join(str(p**k) for p,k in qfac.items()):>12s}={q:<7d} Pi=({npool},{t}){' U FIXED' if fixedU else ''}"
            f"  2^w M={2**w*M:.6f}  2^w max|mu-M|={2**w*err:.3e}")
    if not do_bound:
        return line + f"  [{time.time()-t0:.1f}s]"
    # --- Prop-exact bound ---
    others = [p for p in Qp if p not in qfac]
    Pprime = [p for p in primerange(2, L // 2 + 1) if p * p > L and p not in qfac]
    N1 = len(Pprime)
    js = list(qfac.items())
    total = 0.0; nbad_prim = 0; goodviol = 0; momviol = 0
    for r in range(1, w + 1):
        for S in itertools.combinations(range(w), r):
            for ms in itertools.product(*[range(1, js[j][1] + 1) for j in S]):
                fac = [(js[j][0], m) for j, m in zip(S, ms)]
                G = CharGroup(fac); d = G.d
                dcp = law_c(L, d, others)
                T = G.transform(dcp)                 # E chi(c')
                mask = G.primitive_mask()
                B = math.sqrt(d) / phi(d) * np.sum(np.abs(T[mask])) if mask.any() else 0.0
                weight = 1.0
                for j in range(w):
                    p, k = js[j]
                    if j in S: weight *= 1.0 / (vQ(p, L) + 1)
                    else: weight *= rho0_of(L, p, k)
                total += B * weight
                # A(chi) and bad count, good-lemma check
                cntP = np.zeros(d)
                for p in Pprime: cntP[p % d] += 1
                A = G.transform(cntP)
                bad_all = int(np.sum(A.real > (1 - eta) * N1 + 1e-9))
                if mask.any():
                    nbad_prim += int(np.sum((A.real > (1 - eta) * N1 + 1e-9) & mask))
                    lhs = np.abs(T[mask]); rhs = np.exp(-(N1 - A.real[mask]) / 4)
                    goodviol += int(np.sum(lhs > rhs * (1 + 1e-9) + 1e-15))
                # moment bound for k=1..4
                for kk in range(1, 5):
                    bnd = phi(d) * (1 - eta) ** (-2 * kk) * N1 ** (-kk) * math.factorial(kk) * ((L / 2) ** kk / d + 1)
                    if bad_all > bnd + 1e-9: momviol += 1
    ok = "OK" if err <= total * (1 + 1e-9) + 5e-14 else "VIOLATION"
    return (line + f"\n      Prop-exact bound: 2^w*bound={2**w*total:.3e}  true/bound={err/total if total>0 else float('nan'):.3e} [{ok}]"
            f"  N1={N1}  #bad prim(eta={eta})={nbad_prim}  good-lemma violations={goodviol}  moment-bound violations={momviol}"
            f"  [{time.time()-t0:.1f}s]")

def conj_check(qq):
    fac = [(p, k) for p, k in factorint(qq).items()]
    G = CharGroup(fac)
    units = [r for r in range(qq) if math.gcd(r, qq) == 1]
    idx = {r: G.index(r) for r in units}
    shape = G.fullshape
    chars = list(itertools.product(*[range(o) for o in shape]))
    def chi(t, r):
        a = idx[r % qq]
        return cmath.exp(2j * cmath.pi * sum(ti * ai / o for ti, ai, o in zip(t, a, shape)))
    tau = {t: sum(chi(t, w) * cmath.exp(2j * cmath.pi * w / qq) for w in units) for t in chars}
    e1 = e2 = 0.0
    for b in units:
        for y in units:
            lhs = cmath.exp(2j * cmath.pi * b * y / qq)
            s_conj = sum(chi(t, b * y).conjugate() * tau[t] for t in chars) / len(units)
            s_lit = sum(chi(t, b * y) * tau[t] for t in chars) / len(units)
            e1 = max(e1, abs(lhs - s_conj)); e2 = max(e2, abs(lhs - s_lit))
    return f"q'={qq}: max err conj version={e1:.2e}, literal (no conj) version={e2:.3f}"

if __name__ == "__main__":
    print("# AUD1 exact audit of CMM Prop exact / Lemma good / Lemma moment / conjugation")
    for qq in (15, 77, 45, 28):
        print(conj_check(qq))
    cases = [
        (60, {29: 1, 23: 1}, 4, 2, False), (60, {29: 1, 23: 1}, 4, 2, True),
        (60, {11: 1, 13: 1, 17: 1}, 3, 1, False), (60, {11: 1, 13: 1, 17: 1}, 3, 3, True),
        (100, {47: 1, 43: 1}, 4, 2, False), (100, {11: 1, 13: 1, 17: 1}, 3, 1, False),
        (100, {3: 1, 7: 1, 11: 1}, 3, 2, False),
        (60, {2: 3, 3: 2, 5: 1}, 3, 1, False), (100, {2: 3, 3: 2, 5: 1}, 3, 1, False),
        (60, {3: 2, 5: 1}, 3, 2, False), (60, {2: 2, 7: 1}, 3, 2, False),
        (60, {2: 4, 3: 1}, 3, 2, False), (100, {7: 2, 11: 1}, 4, 2, False),
        (100, {3: 3, 5: 2}, 4, 2, True), (200, {17: 1, 19: 1, 23: 1}, 3, 1, False),
        (300, {19: 1, 23: 1, 29: 1}, 3, 1, False), (300, {149: 1, 139: 1}, 4, 2, False),
        (40, {2: 1, 3: 1, 5: 1, 7: 1}, 3, 1, False), (40, {7: 1, 11: 1, 13: 1, 17: 1}, 2, 1, True),
    ]
    for (L, qf, npl, t, fx) in cases:
        print(audit_case(L, qf, npl, t, fixedU=fx), flush=True)
