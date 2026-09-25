#!/usr/bin/env python3
"""List all a with kappa(a)=H from the level file R_{H-1} (zeros of the bitset in [0,Lambda)).
usage: extract_top.py L Lambda R_{H-1}file out.csv"""
import sys, numpy as np
L = int(sys.argv[1]); lam = int(sys.argv[2]); fn = sys.argv[3]
W = (lam + 63) // 64
mm = np.memmap(fn, dtype=np.uint64, mode='r', shape=(W,))
res = []
CH = 1 << 24
for i0 in range(0, W, CH):
    blk = np.array(mm[i0:i0 + CH])
    idx = np.nonzero(blk != np.uint64(0xFFFFFFFFFFFFFFFF))[0]
    for j in idx:
        x = int(blk[j]); w = i0 + int(j)
        for b in range(64):
            a = 64 * w + b
            if a < lam and not (x >> b) & 1: res.append(a)
with open(sys.argv[4], 'w') as f:
    f.write('a,a_over_Lambda,a_minus_half\n')
    for a in res: f.write(f'{a},{a/lam:.8f},{a - lam//2}\n')
res = np.array(res, dtype=np.float64)
print(f'L={L}: {len(res)} values with kappa=H; min a/Lam={res.min()/lam:.6f}, max a/Lam={res.max()/lam:.6f}; all >= Lam/2: {bool((res >= lam//2).all())}')
q = np.quantile(res / lam, [0, 0.1, 0.25, 0.5, 0.75, 0.9, 1])
print('quantiles of a/Lam:', ' '.join(f'{x:.5f}' for x in q))
