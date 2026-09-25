#!/usr/bin/env python3
"""Validate hbfs (multiset BFS) output for L<=22 against the old 0/1-DP numbers
(p1p4_0924.txt Table 5, 6, 7; lines 6673-7171) and derive per-L summary rows.
Also checks the pointwise shift identity  kappa(Lam/2+b) = 1+kappa(b)  for all b<Lam/2,
which is equivalent to  upperzeros(R_k) == lowerzeros(R_{k-1})  for all k>=1
(because kappa(Lam/2+b) <= 1+kappa(b) always).
usage: validate_small.py  -> writes data/H_table_bfs.csv and prints report."""
import csv, os, sys
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')

H_old = {L: h for L, h in zip(range(2, 23), [1,2,3,4,4,5,5,5,5,6,6,6,6,6,6,7,7,7,7,7,7])}
# Table 5: (#max, min a)
T5 = {2:(1,1),3:(2,4),4:(1,11),5:(2,58),6:(2,58),7:(1,418),8:(9,769),9:(94,2027),10:(94,2027),
      11:(22,26149),12:(22,26149),13:(7553,269323),14:(7553,269323),15:(7553,269323),16:(23748,528083),
      17:(1484,11540143),18:(1484,11540143),19:(1226590,186234043),20:(1226590,186234043),
      21:(1226590,186234043),22:(1226590,186234043)}
# Table 6: fractions of a in [1,Lam) with kappa=k (5 decimals)
T6 = {2:[1.00000],3:[0.60000,0.40000],4:[0.45455,0.45455,0.09091],5:[0.18644,0.45763,0.32203,0.03390],
      7:[0.05489,0.31265,0.44391,0.18616,0.00239],8:[0.03695,0.26341,0.45292,0.23600,0.01073],
      9:[0.01866,0.18896,0.44422,0.31084,0.03732],11:[0.00343,0.07338,0.34669,0.42581,0.14990,0.00079],
      13:[0.00053,0.02360,0.21928,0.45544,0.28020,0.02096],16:[0.00033,0.01778,0.19200,0.44927,0.30767,0.03295],
      17:[0.00004,0.00439,0.09409,0.38243,0.40575,0.11319,0.00012],
      19:[0.00000,0.00096,0.04041,0.28416,0.45432,0.21488,0.00527]}
# Table 7: a_c
T7 = {11:[13,247,3049,12289,26149], 17:[19,1523,83471,1329943,5414023,11540143],
      19:[23,3823,481319,10252523,69837763,186234043]}

def load(L):
    rows = list(csv.DictReader(open(os.path.join(D, 'bfs', f'hbfs_L{L}_levels.csv'))))
    return rows

def main():
    out = []; bad = 0
    for L in range(2, 23):
        rows = load(L)
        lam = int(rows[0]['Lambda']); tau = int(rows[0]['tau'])
        H = int(rows[-1]['k'])
        assert int(rows[-1]['ones_Rk']) == lam
        new = [int(r['new_k']) for r in rows]           # new[0]=1 (a=0)
        ak = [int(r['a_k_first_zero_of_Rkm1']) for r in rows]
        low = [int(r['lowerhalf_zeros_Rk']) for r in rows]
        up = [int(r['upperhalf_zeros_Rk']) for r in rows]
        nmax = new[H]; amin = ak[H]
        ok = (H == H_old[L]) and (T5[L] == (nmax, amin))
        if L in T6:
            fr = [new[k] / (lam - 1) for k in range(1, H + 1)]
            ok6 = all(abs(round(f, 5) - g) < 1e-9 for f, g in zip(fr, T6[L])) and len(fr) == len(T6[L])
            ok = ok and ok6
        if L in T7:
            ok = ok and (ak[2:H+1] == T7[L])
        # half checks
        kh = min(k for k in range(len(rows)) if low[k] == 0)   # max_{a<Lam/2} kappa
        shift = all(up[k] == low[k-1] for k in range(1, H + 1))
        top = (L == 2) or (ak[H] == lam // 2 + ak[H-1])
        if not ok: bad += 1
        out.append(dict(L=L, Lambda=lam, tau=tau, H=H, nmax=nmax, a_H=amin, a_H_over_Lam=f"{amin/lam:.4f}",
                        max_kappa_lower_half=kh, H_eq_1_plus_lowermax=(H == 1 + kh),
                        shift_identity=shift, aH_eq_half_plus_aHm1=top, matches_old_tables=ok,
                        hist=' '.join(str(x) for x in new[1:]), a_c=' '.join(str(x) for x in ak[1:])))
        print(f"L={L:2d} Lam={lam:>10d} tau={tau:4d} H={H} #max={nmax} a_H={amin} "
              f"lowermax={kh} shift={shift} aH=Lam/2+a_(H-1):{top} old_tables_match={ok}")
    with open(os.path.join(D, 'H_table_bfs.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(out[0].keys())); w.writeheader(); w.writerows(out)
    print("mismatches with old tables:", bad)

if __name__ == '__main__':
    main()
