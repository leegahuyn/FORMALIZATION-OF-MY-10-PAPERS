#!/usr/bin/env python3
"""STRUCT numerics for S1 (dedup).
(a) L<=16: distinct-min g_L(a) (0/1 knapsack DP) == multiset-min (BFS sumset levels) for all 0<=a<Lambda_L.
(b) N<=NMAX: property (*) [every odd prime p|N has (p+1)/2 | N] vs. dedup property [multiset-min == distinct-min, all 0<=a<N].
(c) random swap runs for Lambda_L, L<=60: termination, distinctness, sum, #terms, swap counts vs. both potential bounds.
Run: nice -n 10 python3 dedup_check.py > ../out/dedup_check.out
"""
import math, random, sys
import numpy as np
from sympy import primerange, divisors, factorint, isprime

def lcm_upto(L):
    x = 1
    for k in range(1, L + 1):
        x = x * k // math.gcd(x, k)
    return x

INF = 127

def distinct_min(N, D):
    dp = np.full(N, INF, dtype=np.int16)
    dp[0] = 0
    for d in D:
        if d >= N:
            continue
        old = dp.copy()
        np.minimum(dp[d:], old[:-d] + 1, out=dp[d:])
    return dp

def multiset_min(N, D):
    dp = np.full(N, INF, dtype=np.int16)
    reach = np.zeros(N, dtype=bool); reach[0] = True; dp[0] = 0
    k = 0
    while True:
        k += 1
        new = reach.copy()
        for d in D:
            if d >= N:
                continue
            new[d:] |= reach[:-d]
        fresh = new & ~reach
        if not fresh.any():
            break
        dp[fresh] = k
        reach = new
        if k > 60:
            break
    return dp

def part_a():
    print("(a) distinct-min vs multiset-min, all 0<=a<Lambda_L")
    for L in range(2, 17):
        N = lcm_upto(L)
        D = [d for d in divisors(N) if d < N]
        g = distinct_min(N, D)
        gm = multiset_min(N, D)
        eq = bool(np.array_equal(g, gm))
        print(f"  L={L:2d} Lambda={N:7d} tau-1={len(D):3d} H(L)={int(g.max()):2d} equal={eq}")
        assert eq

def star(N):
    for p in factorint(N):
        if p > 2 and N % ((p + 1) // 2) != 0:
            return False
    return True

def part_b(NMAX=2000):
    print(f"(b) property (*) vs dedup property, 2<=N<={NMAX}")
    cnt = {(s, d): 0 for s in (True, False) for d in (True, False)}
    examples_nostar_dedup = []
    cnt_witness = [0]
    first_fail = []
    for N in range(2, NMAX + 1):
        D = [d for d in divisors(N) if d < N]
        g = distinct_min(N, D)
        gm = multiset_min(N, D)
        ded = bool(np.array_equal(g, gm))
        s = star(N)
        cnt[(s, ded)] += 1
        if s and not ded:
            print("  !!! (*) holds but dedup fails at N =", N)
        if not s:
            for p in factorint(N):
                if p > 2 and N % ((p + 1) // 2) != 0:
                    ast = 2 * N // p
                    assert gm[ast] == 2 and g[ast] >= 3, (N, p)
                    cnt_witness[0] += 1
        if (not s) and ded and len(examples_nostar_dedup) < 25:
            examples_nostar_dedup.append(N)
        if (not ded) and len(first_fail) < 12:
            bad = [a for a in range(N) if g[a] != gm[a]]
            first_fail.append((N, bad[:6], [(int(gm[a]), int(g[a]) if g[a] < INF else 'inf') for a in bad[:3]]))
    print(f"  witness a*=2N/p verified (multiset-min 2, distinct-min >=3) for {cnt_witness[0]} pairs (N,p) with (p+1)/2 not dividing N")
    for k, v in cnt.items():
        print(f"  (*)={k[0]!s:5} dedup={k[1]!s:5}: {v}")
    print("  first N where dedup fails: (N, first bad a, [(multiset-min, distinct-min)])")
    for t in first_fail:
        print("   ", t)
    print("  N without (*) but dedup still holds (first 25):", examples_nostar_dedup)
    # the N=10 example explicitly
    N = 10; D = [1, 2, 5]
    sums = sorted({sum(S) for r in range(4) for S in __import__('itertools').combinations(D, r)})
    print("  N=10: distinct subset sums of {1,2,5} =", sums, "; 4 = 2+2 has multiset-min 2")

def exps(L):
    return {p: int(math.floor(math.log(L) / math.log(p) + 1e-12)) for p in primerange(2, L + 1)}

def vp(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k

def dedup_run(terms, L, ap, primes):
    """least-deficient-prime swap; returns (final terms, merges, splits)."""
    from collections import Counter
    c = Counter(terms)
    merges = splits = 0
    while True:
        dup = [d for d, m in c.items() if m >= 2]
        if not dup:
            break
        d = dup[0]
        p = next(q for q in primes if vp(d, q) < ap[q])
        c[d] -= 2
        if c[d] == 0:
            del c[d]
        if p == 2:
            c[2 * d] += 1; merges += 1
        else:
            r = (p + 1) // 2
            assert d % r == 0
            c[p * d // r] += 1; c[d // r] += 1; splits += 1
    return sorted(c.elements()), merges, splits

def part_c(trials=3000, seed=1):
    print("(c) random dedup runs")
    rng = random.Random(seed)
    worst_ratio_R = 0.0
    maxsw = 0
    for t in range(trials):
        L = rng.randint(3, 60)
        N = lcm_upto(L)
        ap = exps(L); primes = sorted(ap)
        # random divisor generator
        def rdiv():
            d = 1
            for p in primes:
                d *= p ** rng.randint(0, ap[p])
            return d
        s = rng.randint(2, 12)
        base = [rdiv() for _ in range(rng.randint(1, 3))]
        terms = [rng.choice(base) if rng.random() < 0.7 else rdiv() for _ in range(s)]
        terms = [d for d in terms if d < N]
        if len(terms) < 2:
            continue
        a = sum(terms)
        if a >= N:
            # rescale: keep small ones
            terms.sort()
            while terms and sum(terms) >= N:
                terms.pop()
            if len(terms) < 2:
                continue
            a = sum(terms)
        out, Mg, Sp = dedup_run(terms, L, ap, primes)
        assert sum(out) == a and len(set(out)) == len(out) and len(out) <= len(terms)
        assert all(N % d == 0 and 0 < d < N for d in out)
        s0 = len(terms)
        assert Mg <= s0 - 1
        Rb = (sum(math.log(d) for d in terms) + (s0 - 1) * math.log(2)) / math.log(4 / 3)
        assert Sp <= Rb + 1e-9
        Phi0 = sum(d * d for d in terms)
        assert Mg + Sp <= (a * a - Phi0) // 2
        if Rb > 0:
            worst_ratio_R = max(worst_ratio_R, Sp / Rb)
        maxsw = max(maxsw, Mg + Sp)
    print(f"  {trials} trials OK (sum, distinct, #terms nonincreasing, proper divisors);"
          f" max swaps={maxsw}; max splits/product-bound={worst_ratio_R:.3f}")
    # baker example N=60, 48=12+12+4+20
    L = 6; ap = exps(L); primes = sorted(ap)
    out, Mg, Sp = dedup_run([12, 12, 4, 20], L, ap, primes)
    print("  N=60: 12+12+4+20 ->", out, "merges", Mg, "splits", Sp)

if __name__ == "__main__":
    part_a()
    part_b(int(sys.argv[1]) if len(sys.argv) > 1 else 2000)
    part_c()
