#!/usr/bin/env python3
"""Backtrack explicit optimal representations from stored BFS levels (hbfs checkpoints).
Bellman (baker Thm 3.5, with repetition, equivalent by dedup): kappa(a)=c  =>  exists d in D*,
d<=a, with a-d in R_{c-1} (and then kappa(a-d)=c-1).  We take the LARGEST such d at each step.
Each representation is verified: sum, divisibility, number of terms, and kappa lower bound
(a not in R_{c-1}).  If terms repeat, the dedup swap of baker Lemma 3.1 is applied and the result
re-verified (this also exercises the dedup theorem on real data).
usage: bt_repr.py L levels_dir H [a1 a2 ...]   (default targets: a_c for c=1..H from the csv)"""
import sys, os, csv, math
import numpy as np
from sympy import primerange

def lam_divs(L):
    lam = 1; pe = []
    for p in primerange(2, L + 1):
        e = int(math.floor(math.log(L) / math.log(p) + 1e-12))
        while p ** (e + 1) <= L: e += 1
        while p ** e > L: e -= 1
        pe.append((p, e)); lam *= p ** e
    divs = [1]
    for p, e in pe:
        divs = [d * p ** k for d in divs for k in range(e + 1)]
    divs.sort()
    return lam, pe, divs[:-1]

def dedup(terms, lam, pe):
    """baker Lemma 3.1 swap until all terms distinct. Returns new list."""
    t = sorted(terms)
    steps = 0
    while True:
        seen = {}
        dup = None
        for x in t:
            if x in seen: dup = x; break
            seen[x] = 1
        if dup is None: return sorted(t, reverse=True), steps
        d = dup
        t.remove(d); t.remove(d)
        # least prime p with v_p(d) < a_p
        for p, e in pe:
            v = 0; y = d
            while y % p == 0: y //= p; v += 1
            if v < e: break
        if p == 2:
            t += [2 * d]
        else:
            r = (p + 1) // 2
            assert d % r == 0
            t += [p * d // r, d // r]
        steps += 1
        assert all(lam % x == 0 and x < lam for x in t)

def main():
    L = int(sys.argv[1]); ldir = sys.argv[2]; H = int(sys.argv[3])
    lam, pe, divs = lam_divs(L)
    W = (lam + 63) // 64
    R = {0: None}
    for k in range(1, H):
        R[k] = np.memmap(os.path.join(ldir, f'L{L}_R{k}.bin'), dtype=np.uint64, mode='r', shape=(W,))
    def inR(k, a):
        if k == 0: return a == 0
        return (int(R[k][a >> 6]) >> (a & 63)) & 1 == 1
    if len(sys.argv) > 4:
        targets = [(None, int(x)) for x in sys.argv[4:]]
    else:
        here = os.path.dirname(os.path.abspath(__file__))
        rows = list(csv.DictReader(open(os.path.join(here, '..', 'data', 'bfs', f'hbfs_L{L}_levels.csv'))))
        targets = [(int(r['k']), int(r['a_k_first_zero_of_Rkm1'])) for r in rows if int(r['k']) >= 1]
    for c0, a in targets:
        # kappa(a): smallest k with a in R_k (R_H = everything)
        c = next((k for k in range(0, H) if inR(k, a)), H)
        if c0 is not None: assert c == c0, (c, c0)
        terms = []; r = a; cc = c
        while cc > 0:
            for d in reversed(divs):
                if d <= r and inR(cc - 1, r - d):
                    terms.append(d); r -= d; cc -= 1; break
            else:
                raise RuntimeError('backtrack failed')
        assert r == 0 and sum(terms) == a and all(lam % d == 0 and d < lam for d in terms) and len(terms) == c
        lower_ok = (c == 0) or not inR(c - 1, a)
        dd, steps = dedup(terms, lam, pe)
        assert sum(dd) == a and len(dd) <= c and len(set(dd)) == len(dd)
        frac = [f'Lam/{lam // d}' if lam % d == 0 and (lam // d) * d == lam else '' for d in terms]
        print(f'L={L} a={a} kappa={c} (a notin R_{c-1}: {lower_ok}) repr: ' + ' + '.join(map(str, terms)) +
              f'   distinct={len(set(terms)) == len(terms)} dedup_steps={steps}' +
              ('' if steps == 0 else '  deduped: ' + ' + '.join(map(str, dd))))
        print('      as Lam/m: ' + ' + '.join(frac))

if __name__ == '__main__':
    main()
