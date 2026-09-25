#!/usr/bin/env python3
"""AUD2 independent numerics for STRUCT S1 (dedup), different algorithm from STRUCT:
big-integer bitsets (bit a set <=> a reachable), layered by number of terms.
(A) Lambda_L, L<=13: level sets of distinct-min (0/1, layered bitsets) == multiset-min (sumset BFS).
(B) 2<=N<=NMAX: (*) <=> dedup property; witness a*=2N/p for every failing (N,p).
(C) swap algorithm with a DIFFERENT duplicate-selection rule (largest duplicate first, and random),
    adversarial inputs (many copies of one divisor), L up to 120; check both swap-count bounds.
(D) Newton identity 24 e4 = p1^4 - 6 p1^2 p2 + 3 p2^2 + 8 p1 p3 - 6 p4 on random sets.
Run: nice -n 10 python3 aud2_dedup.py > ../out/aud2_dedup.out
"""
import math, random, sys, itertools
from sympy import divisors, factorint, primerange

def lcm_upto(L):
    x = 1
    for k in range(1, L + 1):
        x = x * k // math.gcd(x, k)
    return x

def levels_distinct(N, D, kmax=80):
    """B[k] = bitset of sums of <=k DISTINCT elements of D, restricted to [0,N)."""
    mask = (1 << N) - 1
    B = [1]  # B[0] = {0}
    for d in D:
        # extend list lazily
        if len(B) < kmax:
            B.append(B[-1])
        for k in range(len(B) - 1, 0, -1):
            B[k] = (B[k] | (B[k - 1] << d)) & mask
    # make monotone closure (B[k] should already be monotone)
    return B

def levels_multi(N, D, kmax=80):
    mask = (1 << N) - 1
    R = [1]
    while len(R) <= kmax:
        cur = R[-1]
        new = cur
        for d in D:
            new |= (cur << d)
        new &= mask
        if new == cur:
            break
        R.append(new)
    return R

def first_level(B, a):
    for k, b in enumerate(B):
        if (b >> a) & 1:
            return k
    return math.inf

def star(N):
    return all(p == 2 or N % ((p + 1) // 2) == 0 for p in factorint(N))

def part_A():
    print("(A) Lambda_L: distinct-min == multiset-min for all 0<=a<Lambda_L (bitset levels)")
    for L in range(2, 14):
        N = lcm_upto(L)
        D = [d for d in divisors(N) if d < N]
        Bd = levels_distinct(N, D, kmax=12)
        Bm = levels_multi(N, D, kmax=12)
        full = (1 << N) - 1
        Hd = next(k for k, b in enumerate(Bd) if b == full)
        Hm = next(k for k, b in enumerate(Bm) if b == full)
        same = all(Bd[k] == Bm[k] for k in range(min(len(Bm), Hd + 1)))
        print(f"  L={L:2d} N={N:7d} H_distinct={Hd} H_multiset={Hm} all level sets equal={same}")
        assert same and Hd == Hm

def part_B(NMAX):
    print(f"(B) 2<=N<={NMAX}: (*) <=> dedup, and witness a*=2N/p")
    cnt = {}
    wit = 0
    for N in range(2, NMAX + 1):
        D = [d for d in divisors(N) if d < N]
        kmax = 40
        Bd = levels_distinct(N, D, kmax=kmax)
        Bm = levels_multi(N, D, kmax=kmax)
        # dedup property: for each k, sums with <=k repeated terms == sums with <=k distinct terms
        # compare up to the multiset saturation level
        # distinct-level sets are subsets of multiset-level sets; dedup <=> equality at every level
        # (levels beyond multiset saturation add nothing, since distinct sums are multiset sums)
        K = len(Bm) - 1
        ded = all(Bd[min(k, len(Bd) - 1)] == Bm[k] for k in range(K + 1))
        s = star(N)
        cnt[(s, ded)] = cnt.get((s, ded), 0) + 1
        if not s:
            for p in factorint(N):
                if p > 2 and N % ((p + 1) // 2) != 0:
                    a = 2 * N // p
                    km = first_level(Bm, a)
                    kd = first_level(Bd, a)
                    assert km == 2 and kd >= 3, (N, p, km, kd)
                    wit += 1
    for k in sorted(cnt):
        print(f"  (*)={k[0]!s:5} dedup={k[1]!s:5}: {cnt[k]}")
    print(f"  witness a*=2N/p: multiset-min 2 and distinct-min >=3 verified for {wit} pairs (N,p)")

def exps(L):
    return {p: int(math.floor(math.log(L) / math.log(p) + 1e-12)) for p in primerange(2, L + 1)}

def vp(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k

def swap_run(terms, ap, primes, rule, rng):
    from collections import Counter
    c = Counter(terms)
    Mg = Sp = 0
    while True:
        dup = [d for d, m in c.items() if m >= 2]
        if not dup:
            break
        d = max(dup) if rule == "max" else (min(dup) if rule == "min" else rng.choice(dup))
        p = next(q for q in primes if vp(d, q) < ap[q])
        c[d] -= 2
        if c[d] == 0:
            del c[d]
        if p == 2:
            c[2 * d] += 1; Mg += 1
        else:
            r = (p + 1) // 2
            assert d % r == 0
            u, v = p * d // r, d // r
            assert u + v == 2 * d and u * v * (p + 1) ** 2 == 4 * p * d * d
            c[u] += 1; c[v] += 1; Sp += 1
    return sorted(c.elements()), Mg, Sp

def part_C(trials=2500, seed=7):
    print("(C) swap algorithm, rules max/min/random, adversarial repeated inputs")
    rng = random.Random(seed)
    worst = 0.0; maxsw = 0; worst_phi = 0.0
    for t in range(trials):
        L = rng.randint(3, 120)
        N = lcm_upto(L); ap = exps(L); primes = sorted(ap)
        def rdiv():
            d = 1
            for p in primes:
                if rng.random() < 0.5:
                    d *= p ** rng.randint(0, ap[p])
            return d
        mode = rng.random()
        if mode < 0.4:
            d = rdiv(); s = rng.randint(2, 60)
            terms = [d] * s
        else:
            base = [rdiv() for _ in range(rng.randint(1, 4))]
            terms = [rng.choice(base) for _ in range(rng.randint(2, 40))]
        terms = [d for d in terms if d < N]
        while terms and sum(terms) >= N:
            terms.pop()
        if len(terms) < 2:
            continue
        a = sum(terms); s0 = len(terms)
        rule = rng.choice(["max", "min", "rand"])
        out, Mg, Sp = swap_run(terms, ap, primes, rule, rng)
        assert sum(out) == a and len(set(out)) == len(out) and len(out) <= s0
        assert all(N % d == 0 and 0 < d < N for d in out)
        assert Mg <= s0 - 1
        Rb = (sum(math.log(d) for d in terms) + (s0 - 1) * math.log(2)) / math.log(4 / 3)
        assert Sp <= Rb + 1e-9, (Sp, Rb)
        Phi0 = sum(d * d for d in terms)
        assert 2 * (Mg + Sp) <= a * a - Phi0
        if Rb > 0: worst = max(worst, Sp / Rb)
        maxsw = max(maxsw, Mg + Sp)
    print(f"  {trials} trials OK; max swaps={maxsw}; max splits/(product bound)={worst:.3f}")
    # extreme: 2^k copies of 1 in Lambda_L
    for L in (10, 30, 60):
        N = lcm_upto(L); ap = exps(L); primes = sorted(ap)
        s = min(500, N - 1)
        out, Mg, Sp = swap_run([1] * s, ap, primes, "max", rng)
        print(f"  L={L}: {s} copies of 1 -> {len(out)} distinct terms, merges={Mg}, splits={Sp}")

def part_D():
    rng = random.Random(3)
    ok = True
    for _ in range(200):
        S = rng.sample(range(1, 60), rng.randint(4, 12))
        p = [sum(x ** k for x in S) for k in range(5)]
        e4 = sum(a * b * c * d for a, b, c, d in itertools.combinations(S, 4))
        ok &= (24 * e4 == p[1] ** 4 - 6 * p[1] ** 2 * p[2] + 3 * p[2] ** 2 + 8 * p[1] * p[3] - 6 * p[4])
    print("(D) Newton identity 24e4 = p1^4-6p1^2p2+3p2^2+8p1p3-6p4 on 200 random sets:", ok)

if __name__ == "__main__":
    part_A()
    part_B(int(sys.argv[1]) if len(sys.argv) > 1 else 3000)
    part_C()
    part_D()
