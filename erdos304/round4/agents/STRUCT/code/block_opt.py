#!/usr/bin/env python3
"""STRUCT numerics for S2: optimal lower bound for Lambda-type block schemes.

For a chain 1 | Lambda_{y_1} | ... | Lambda_{y_t} = Lambda_L (y_j prime powers, Lambda strictly increasing),
block j>=2 needs  binom(D_j + K_j, K_j) >= b_j,  D_j = #{e | Lambda_{y_j} : 1 <= e < b_j},
and block 1 needs K_1 >= H(y_1) >= Hlow(y_1) (exact H for y<=22 from the corpus, else the entropy bound).
We compute an UPPER bound for D_j by a floor-rounded log-histogram (rounding every log p^j down to the grid
can only increase counts below a threshold), hence a rigorous LOWER bound for K_j, and minimise
sum K_j by dynamic programming over all chains with nu_j = log b_j / psi(y_j) <= w for j >= 2.
Compared with c(w)(log L)^2, c(w) = 1/(2(1+log(1/w)) log(1/(1-w))).
Run: nice -n 10 python3 block_opt.py > ../out/block_opt.out
"""
import math, sys
import numpy as np
from sympy import primerange

HEXACT = {2: 1, 3: 2, 4: 3, 5: 4, 6: 4, 7: 5, 8: 5, 9: 5, 10: 5, 11: 6, 12: 6, 13: 6, 14: 6, 15: 6,
          16: 6, 17: 7, 18: 7, 19: 7, 20: 7, 21: 7, 22: 7}

def lbinom(n, k):
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)

def kmin(D, logb):
    """least K with binom(D+K, K) >= b (D may be a float upper bound).
    log binom(D+K,K) = sum_{i<=K} log((D+i)/i), accumulated directly (no lgamma cancellation)."""
    if logb <= 0:
        return 0
    K, acc = 0, 0.0
    while acc < logb - 1e-12:
        K += 1
        acc += math.log1p(D / K)
    return K

def c_w(w):
    return 1.0 / (2 * (1 + math.log(1 / w)) * math.log(1 / (1 - w)))

def run(Lmax, ws, h=0.02, y1max=None):
    primes = list(primerange(2, Lmax + 1))
    pp = sorted((p ** k, p) for p in primes for k in range(1, 64) if p ** k <= Lmax)
    ys = [m for m, _ in pp]
    psi = np.cumsum([math.log(p) for _, p in pp])      # psi(y_i)
    n = len(ys)
    wmax = max(ws)
    # exponent tables a_p(y_i)
    results = {}
    # histograms (cumulative counts below grid index) for each endpoint, truncated at wmax*psi
    cums = []
    ap = {}
    for i, (m, p) in enumerate(pp):
        ap[p] = ap.get(p, 0) + 1
        nb = int(math.ceil(wmax * psi[i] / h)) + 2
        hist = np.zeros(nb)
        hist[0] = 1.0
        for q, a in ap.items():
            lq = math.log(q)
            new = hist.copy()
            for j in range(1, a + 1):
                s = int(math.floor(j * lq / h))
                if s >= nb:
                    break
                new[s:] += hist[:nb - s]
            hist = new
        cums.append(np.cumsum(hist))
    tau_log = []  # log tau(Lambda_y)
    ap = {}
    for i, (m, p) in enumerate(pp):
        ap[p] = ap.get(p, 0) + 1
        tau_log.append(sum(math.log(a + 1) for a in ap.values()))
    def Hlow(i):
        y = ys[i]
        if y1max is not None and y > y1max:
            return 10 ** 9
        if y in HEXACT:
            return HEXACT[y]
        return kmin(math.exp(tau_log[i]) - 1, psi[i])
    for w in ws:
        best = [0] * n
        for i in range(n):
            b = Hlow(i)
            for k in range(i):
                logb = psi[i] - psi[k]
                if logb > w * psi[i] + 1e-12:
                    continue
                idx = int(math.ceil(logb / h)) - 1
                D = cums[i][min(idx, len(cums[i]) - 1)]   # upper bound for #{e | Lambda_y : 1 <= e < b}
                K = kmin(D, logb)
                if best[k] + K < b:
                    b = best[k] + K
            best[i] = b
        results[w] = best
    return ys, psi, results

if __name__ == "__main__":
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    ws = [0.25, 0.5, 0.75, 0.9]
    checkpoints = [50, 100, 200, 500, 1000, 2000, 3000, 5000, 10000, 20000]
    print("Rigorous (up to float rounding) lower bound for sum K_j over Lambda-type block schemes")
    print("with nu_j = log b_j/psi(y_j) <= w for j >= 2; first block y_1 restricted as stated, cost >= H(y_1).")
    print("Entry: DP bound [c(w)((log L)^2-(log y1max)^2)] ; c(w)=1/(2(1+log(1/w))log(1/(1-w)))")
    for label, y1 in (("y_1 <= 22 (exact H known)", 22), ("y_1 unrestricted (single block allowed)", None)):
        ys, psi, res = run(Lmax, ws, y1max=y1)
        print("--", label)
        for L in checkpoints:
            if L > Lmax:
                break
            i = max(k for k, y in enumerate(ys) if y <= L)
            row = f"L={L:6d} logL={math.log(L):5.2f} "
            for w in ws:
                ref = c_w(w) * (math.log(L) ** 2 - (math.log(y1) ** 2 if y1 else math.log(L) ** 2))
                row += f"| w={w}: {res[w][i]:3d} [{ref:6.1f}] "
            print(row, flush=True)
    print("c(w):", {w: round(c_w(w), 4) for w in ws})
