#!/usr/bin/env python3
"""
AUD1: sanity check of the Parseval lower bound for the Prop-exact error bound (audit Prop AUD1:prop-parseval):
for squarefree q = p_1...p_w with v_j = 1,
   Bfrak(q) := sum_{S != 0} B(S) 2^{-|S|} prod_{j notin S} rho0_j  >=  2^{-w} q^{-1/2} (phi(q)/N - 1),
N = #supp(c' mod q) <= tau(Q').  Also compares with 2^{-w} and with the true max|mu - M|.
Usage: nice -n 10 python3 aud1_parseval.py > ../out/aud1_parseval.txt
"""
import itertools, math, time
import numpy as np
from sympy import primerange
from aud1_exact import (vQ, qprimes, poolp, law_c, law_U, mult_conv, mu_direct, M_of, rho0_of,
                        CharGroup, phi)

def run(L, qs, npool, t):
    q = math.prod(qs); w = len(qs)
    for p in qs: assert vQ(p, L) == 1
    Qp = qprimes(L); others = [p for p in Qp if p not in qs]
    t0 = time.time()
    dcq = law_c(L, q, others)
    N = int(np.count_nonzero(dcq > 0))
    tauQp = math.prod(vQ(p, L) + 1 for p in others)
    Bfrak = 0.0
    for r in range(1, w + 1):
        for S in itertools.combinations(range(w), r):
            fac = [(qs[j], 1) for j in S]
            G = CharGroup(fac); d = G.d
            T = G.transform(law_c(L, d, others)); mask = G.primitive_mask()
            B = math.sqrt(d) / phi(d) * np.sum(np.abs(T[mask]))
            wt = 2.0 ** (-r) * math.prod(rho0_of(L, qs[j], 1) for j in range(w) if j not in S)
            Bfrak += B * wt
    lower = 2.0 ** (-w) * q ** -0.5 * (phi(q) / N - 1)
    dX = mult_conv(dcq, law_U(q, poolp(L)[:npool], t), q)
    units = [b for b in range(1, q) if math.gcd(b, q) == 1]
    err = np.max(np.abs(mu_direct(dX, q, units) - M_of(L, {p: 1 for p in qs})))
    print(f"L={L} q={'*'.join(map(str,qs))}={q} N=#supp(c' mod q)={N} tau(Q')={tauQp}: "
          f"2^w*Bfrak={2**w*Bfrak:.4f} >= 2^w*lower={2**w*lower:.4f} [{'OK' if Bfrak >= lower - 1e-12 else 'FAIL'}];"
          f" 2^w*true max|mu-M|={2**w*err:.4f}; sqrt(q)/(2 tau(Q'))={math.sqrt(q)/(2*tauQp):.3f} [{time.time()-t0:.1f}s]", flush=True)

if __name__ == "__main__":
    print("# AUD1 Parseval lower bound check")
    run(40, [7, 11, 13, 17], 2, 1)
    run(60, [11, 13, 17, 19], 2, 1)
    run(40, [7, 11, 13, 17, 19], 2, 1)
