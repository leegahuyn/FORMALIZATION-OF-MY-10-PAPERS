#!/usr/bin/env python3
"""Explicit optimal representations for L=25 without all BFS levels.
Inputs: kap_small (uint8 kappa(r) for r < X = 2^30, written by hbfs2 -K) and optionally a level
file R_k (bitset).  For a target a with kappa(a)=c (known from the BFS csv), a depth-first search
over the large terms d1 >= d2 >= ... (largest first; a term must be >= r/budget) stops as soon as
the remainder r < X and kap_small[r] <= remaining budget; the small part is then backtracked with
the Bellman relation inside [0,X).  Any representation with c terms is optimal because kappa(a)=c is
certified by the BFS (a not in R_{c-1}).  Every output is verified (sum, divisibility, #terms) and
deduplicated with baker Lemma 3.1 if needed.
usage: repr_dfs.py L kapfile [a ...]   (default: a_c from data/bfs/hbfs2_L<L>_levels.csv)"""
import sys, os, csv, math
import numpy as np
from bt_repr import lam_divs, dedup
sys.setrecursionlimit(10000)

def main():
    L = int(sys.argv[1]); kf = sys.argv[2]
    lam, pe, divs = lam_divs(L)
    kap = np.memmap(kf, dtype=np.uint8, mode='r'); X = len(kap)
    here = os.path.dirname(os.path.abspath(__file__))
    rows = list(csv.DictReader(open(os.path.join(here, '..', 'data', 'bfs', f'hbfs2_L{L}_levels.csv'))))
    targets = [(int(r['k']), int(r['a_k_first_zero_of_Rkm1'])) for r in rows if int(r['k']) >= 1]
    if len(sys.argv) > 3:
        want = set(int(x) for x in sys.argv[3:]); targets = [t for t in targets if t[1] in want]
    divs_desc = divs[::-1]
    def small_repr(r):
        out = []
        c = int(kap[r])
        while r > 0:
            for d in divs_desc:
                if d <= r and int(kap[r - d]) == c - 1:
                    out.append(d); r -= d; c -= 1; break
        return out
    nodes = [0]
    def dfs(r, budget):
        nodes[0] += 1
        if r < X:
            return small_repr(r) if int(kap[r]) <= budget else None
        if budget == 0: return None
        for d in divs_desc:
            if d > r: continue
            if d * budget < r: break
            res = dfs(r - d, budget - 1)
            if res is not None: return [d] + res
        return None
    for c, a in targets:
        nodes[0] = 0
        rep = dfs(a, c)
        assert rep is not None and sum(rep) == a and len(rep) <= c and all(lam % d == 0 and d < lam for d in rep)
        dd, steps = dedup(rep, lam, pe)
        print(f"L={L} a_{c}={a}: {len(rep)} terms: " + ' + '.join(map(str, rep)) +
              f"  distinct={len(set(rep)) == len(rep)} (dedup steps {steps}) [dfs nodes {nodes[0]}]")
        print('      = ' + ' + '.join(f'Lam/{lam // d}' for d in rep))

if __name__ == '__main__':
    main()
