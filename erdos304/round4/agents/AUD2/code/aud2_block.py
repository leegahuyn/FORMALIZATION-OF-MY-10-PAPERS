#!/usr/bin/env python3
"""AUD2 independent numerics for STRUCT S2/S3.
(1) c(w) values; G_kappa(nu) decreasing on (0,1) for kappa in {1,1.5,3} (grid check).
(2) Lemma divcount vs EXACT divisor counts of Lambda_y (meet-in-the-middle), y in {30,50,80,100}.
(3) DP lower bound for Lambda-type block schemes with EXACT D_j (meet in the middle; an upper
    count #{e | Lambda_y : log e < log b + 1e-9} >= D_j, hence a valid lower bound for K_j),
    y_1 <= 22, nu_j <= w, compared with STRUCT's rounded-histogram DP (must be >=).
(4) pi(t) <= 3t/log t (2<=t<=2e6); psi(y)-theta(y) <= sqrt(y)(log y)^2 (2<=y<=2e6).
Run: nice -n 10 python3 aud2_block.py > ../out/aud2_block.out
"""
import math, bisect
import numpy as np
from sympy import primerange

HEXACT = {2: 1, 3: 2, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 5, 10: 5, 11: 6, 12: 6, 13: 6, 14: 6, 15: 6,
          16: 6, 17: 7, 18: 7, 19: 7, 20: 7, 21: 7, 22: 7}

def c_w(w):
    return 1.0 / (2 * (1 + math.log(1 / w)) * math.log(1 / (1 - w)))

def G_k(nu, k):
    return 1.0 / ((math.log(1 / nu) + k) * math.log(1 / (1 - nu)))

def part1():
    print("(1) c(w):", {w: round(c_w(w), 4) for w in (0.25, 0.5, 0.75, 0.9)})
    for k in (1.0, 1.5, 3.0):
        grid = np.linspace(1e-4, 1 - 1e-4, 20001)
        vals = np.array([G_k(x, k) for x in grid])
        print(f"    kappa={k}: G_kappa strictly decreasing on grid: {bool(np.all(np.diff(vals) < 0))}")
    # asymptotics
    for w in (1e-3, 1e-5):
        print(f"    w={w}: c(w)*2w*log(1/w) = {c_w(w) * 2 * w * math.log(1 / w):.4f} (->1)")
    for w in (1 - 1e-3, 1 - 1e-6):
        print(f"    w={w}: c(w)*2*log(1/(1-w)) = {c_w(w) * 2 * math.log(1 / (1 - w)):.4f} (->1)")

def lam_exps(y):
    return {p: int(math.floor(math.log(y) / math.log(p) + 1e-12)) for p in primerange(2, y + 1)}

def split_logs(y):
    """logs of divisors of Lambda_y, split: A = primes <= sqrt(y) (all exponents), B = primes > sqrt(y)."""
    ex = lam_exps(y)
    A = np.array([0.0]); B = np.array([0.0])
    for p, a in ex.items():
        lp = math.log(p)
        if p * p <= y:
            A = np.concatenate([A + j * lp for j in range(a + 1)])
        else:
            B = np.concatenate([B, B + lp])
    A.sort(); B.sort()
    return A, B

def count_below(A, B, t):
    """#{(a,b): a+b < t}  (upper count: t already includes tolerance)."""
    return int(np.searchsorted(B, t - A, side="left").sum())

def pi_(x, primes):
    return bisect.bisect_right(primes, x)

def part2():
    print("(2) Lemma divcount: exact log#{e|Lambda_y: e<=e^u} vs bound m0*log(e*pi/m0)+pi(y^(1-eta))*log(1+log2 y)")
    primes = list(primerange(2, 10 ** 5))
    for y in (30, 50, 80, 100):
        A, B = split_logs(y)
        psi = sum(math.log(p) * a for p, a in lam_exps(y).items())
        for eta in (0.5, 0.3):
            for v in (0.1, 0.25, 0.5):
                u = v * psi
                m0 = u / ((1 - eta) * math.log(y))
                if m0 > pi_(y, primes):
                    continue
                exact = math.log(count_below(A, B, u + 1e-9))
                bound = m0 * math.log(math.e * pi_(y, primes) / m0) + pi_(y ** (1 - eta), primes) * math.log(1 + math.log2(y))
                print(f"    y={y:3d} eta={eta} v={v}: exact={exact:7.3f} bound={bound:7.3f} ok={exact <= bound + 1e-9}")
                assert exact <= bound + 1e-9

def kmin(D, logb):
    if logb <= 0:
        return 0
    K, acc = 0, 0.0
    while acc < logb - 1e-12:
        K += 1
        acc += math.log1p(D / K)
    return K

def part3(Lmax=100, ws=(0.25, 0.5, 0.75, 0.9)):
    print(f"(3) exact-count DP lower bound for Lambda-type schemes, y_1<=22, L<={Lmax}")
    primes = list(primerange(2, Lmax + 1))
    pp = sorted((p ** k, p) for p in primes for k in range(1, 40) if p ** k <= Lmax)
    ys = [m for m, _ in pp]
    psi = np.cumsum([math.log(p) for _, p in pp])
    splits = [split_logs(y) for y in ys]
    n = len(ys)
    res = {}
    for w in ws:
        best = [0] * n
        for i in range(n):
            b = HEXACT.get(ys[i], 10 ** 9) if ys[i] <= 22 else 10 ** 9
            A, B = splits[i]
            for k in range(i):
                logb = psi[i] - psi[k]
                if logb > w * psi[i] + 1e-12:
                    continue
                D = count_below(A, B, logb + 1e-9) - 1  # remove e=... (count includes e=1); D_j counts 1<=e<b: keep e=1, drop nothing? see below
                D = D + 1  # conservative: use the full upper count (includes e=1 and possibly e=b)
                K = kmin(D, logb)
                b = min(b, best[k] + K)
            best[i] = b
        res[w] = best
    for L in (50, 100):
        if L > Lmax:
            continue
        i = max(k for k, y in enumerate(ys) if y <= L)
        row = "    L=%d: " % L + "  ".join(f"w={w}: {res[w][i]}" for w in ws)
        print(row)
    print("    STRUCT (rounded histogram, weaker D bound): L=50: 15,11,8,7; L=100: 20,13,11,9")

def part4(X=2 * 10 ** 6):
    print("(4) elementary prime bounds up to", X)
    sieve = np.ones(X + 1, dtype=bool); sieve[:2] = False
    for p in range(2, int(X ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    pr = np.nonzero(sieve)[0]
    pic = np.cumsum(sieve)
    t = np.arange(2, X + 1)
    ok1 = bool(np.all(pic[2:] <= 3 * t / np.log(t)))
    worst1 = float(np.max(pic[2:] * np.log(t) / t))
    # psi - theta = sum over prime powers p^k, k>=2, of log p
    extra = np.zeros(X + 1)
    for p in pr:
        q = p * p
        if q > X:
            break
        while q <= X:
            extra[q] += math.log(p)
            q *= p
    diff = np.cumsum(extra)
    ok2 = bool(np.all(diff[2:] <= np.sqrt(t) * np.log(t) ** 2))
    print(f"    pi(t) <= 3t/log t: {ok1} (max pi(t)log t/t = {worst1:.4f}); psi-theta <= sqrt(y)(log y)^2: {ok2}")

if __name__ == "__main__":
    part1()
    part2()
    part3()
    part4()
