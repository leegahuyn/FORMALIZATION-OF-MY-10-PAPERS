#!/usr/bin/env python3
"""Generate the LaTeX (booktabs) tables of agents/NUM/frag.tex directly from the CSV data.
Writes out/tables/<name>.tex ; frag.tex is assembled by code/assemble_frag.py (placeholders %%name%%)."""
import csv, os, math, re, glob
here = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(here, '..', 'data'); O = os.path.join(here, '..', 'out', 'tables')
os.makedirs(O, exist_ok=True)

def levels(prefix):
    return list(csv.DictReader(open(os.path.join(D, 'bfs', prefix + '_levels.csv'))))

def num(x):
    s = str(x); out = ''
    # thin space grouping
    s = s[::-1]; parts = [s[i:i+3] for i in range(0, len(s), 3)]
    return '\\,'.join(p[::-1] for p in parts[::-1])

def entropy_lb(lam, tau):
    return math.log(lam - 1) / math.log(tau)

# ---------- Table: H(L) for all L <= 25
def t_H():
    rows = []
    bfs = {}
    for L in range(2, 26):
        for pre in (f'hbfs_L{L}', f'hbfs2_L{L}'):
            p = os.path.join(D, 'bfs', pre + '_levels.csv')
            if os.path.exists(p):
                r = levels(pre)
                if int(r[-1]['ones_Rk']) == int(r[-1]['Lambda']):
                    bfs[L] = r; break
    if 23 in bfs: bfs[24] = bfs[23]
    if 25 in bfs: bfs[26] = bfs[25]
    s = ['\\begin{tabular}{rrrrrrrrr}', '\\toprule',
         '$L$ & $\\Lambda_L$ & $\\tau(\\Lambda_L)$ & $H(L)$ & $\\#\\{\\kappa=H\\}$ & $a_H$ & $a_H/\\Lambda_L$ & $H/\\ln L$ & $\\frac{\\ln(\\Lambda_L-1)}{\\ln\\tau}$\\\\', '\\midrule']
    prev = None
    for L in sorted(bfs):
        r = bfs[L]; lam = int(r[0]['Lambda']); tau = int(r[0]['tau']); H = int(r[-1]['k'])
        if lam == prev: continue
        prev = lam
        nmax = int(r[-1]['new_k']); aH = int(r[-1]['a_k_first_zero_of_Rkm1'])
        Ls = str(L)
        same = [l for l in bfs if int(bfs[l][0]['Lambda']) == lam]
        if len(same) > 1: Ls = f'{min(same)}--{max(same)}'
        s.append(f'{Ls} & {num(lam)} & {tau} & {H} & {num(nmax)} & {num(aH)} & {aH/lam:.4f} & {H/math.log(max(same)):.3f} & {entropy_lb(lam,tau):.3f}\\\\')
    s += ['\\bottomrule', '\\end{tabular}']
    return '\n'.join(s)

# ---------- per-level table for a given L
def t_levels(pre):
    r = levels(pre); lam = int(r[0]['Lambda']); half = lam // 2
    s = ['\\begin{tabular}{rrrrrr}', '\\toprule',
         '$k$ & $|R_k|$ & $\\#\\{a:\\kappa(a)=k\\}$ & $a_k$ & $\\#([0,\\frac{\\Lambda}{2})\\setminus R_k)$ & $\\#([\\frac{\\Lambda}{2},\\Lambda)\\setminus R_k)$\\\\', '\\midrule']
    for x in r:
        k = int(x['k'])
        s.append(f"{k} & {num(x['ones_Rk'])} & {num(x['new_k'])} & {num(x['a_k_first_zero_of_Rkm1'])} & {num(x['lowerhalf_zeros_Rk'])} & {num(x['upperhalf_zeros_Rk'])}\\\\")
    s += ['\\bottomrule', '\\end{tabular}']
    return '\n'.join(s)

# ---------- kappa fraction table (Table 6 style) incl. 23, 25
def t_frac():
    Ls = [11, 13, 16, 17, 19, 23, 25]
    data = {}
    for L in Ls:
        for pre in (f'hbfs_L{L}', f'hbfs2_L{L}'):
            p = os.path.join(D, 'bfs', pre + '_levels.csv')
            if os.path.exists(p):
                r = levels(pre)
                if int(r[-1]['ones_Rk']) == int(r[-1]['Lambda']): data[L] = r; break
    K = max(int(r[-1]['k']) for r in data.values())
    s = ['\\begin{tabular}{r' + 'r' * K + '}', '\\toprule', '$L$ & ' + ' & '.join(f'$k={k}$' for k in range(1, K + 1)) + '\\\\', '\\midrule']
    for L in Ls:
        if L not in data: continue
        r = data[L]; lam = int(r[0]['Lambda'])
        fr = [int(x['new_k']) / (lam - 1) for x in r[1:]]
        def ff(f):
            if 0 < f < 5e-6:
                e = int(math.floor(math.log10(f))); return f'${f / 10 ** e:.1f}\\cdot10^{{{e}}}$'
            return f'{f:.5f}'
        s.append(f'{L} & ' + ' & '.join(ff(f) for f in fr) + ' & ' * (K - len(fr)) + '\\\\')
    s += ['\\bottomrule', '\\end{tabular}']
    return '\n'.join(s)

# ---------- dyadic max-kappa profile
def dyadic_profile(pre):
    # positional read (the header field name 'zeros_Rk_in_[lo,hi)' contains a comma)
    raw = list(csv.reader(open(os.path.join(D, 'bfs', pre + '_dyadic.csv'))))[1:]
    rows = [dict(k=x[1], j=x[2], z=x[5]) for x in raw]
    H = max(int(x['k']) for x in rows)
    J = sorted(set(int(x['j']) for x in rows))
    mk = {}
    for j in J:
        # max kappa on [2^j,2^{j+1}) = smallest k with zero count 0
        ks = [int(x['k']) for x in rows if int(x['j']) == j and int(x['z']) == 0]
        mk[j] = min(ks) if ks else H
    # compress runs
    runs = []; start = J[0]
    for j in J[1:] + [None]:
        if j is None or mk[j] != mk[start]:
            end = (j - 1) if j is not None else J[-1]
            runs.append((start, end, mk[start])); start = j
    return runs

if __name__ == '__main__':
    open(os.path.join(O, 'H.tex'), 'w').write(t_H())
    for L in (23, 25):
        for pre in (f'hbfs_L{L}', f'hbfs2_L{L}'):
            p = os.path.join(D, 'bfs', pre + '_levels.csv')
            if os.path.exists(p) and int(levels(pre)[-1]['ones_Rk']) == int(levels(pre)[-1]['Lambda']):
                open(os.path.join(O, f'levels{L}.tex'), 'w').write(t_levels(pre))
                runs = dyadic_profile(pre)
                open(os.path.join(O, f'dyadic{L}.txt'), 'w').write('; '.join(f'j={a}..{b}: {k}' for a, b, k in runs))
                print(L, runs)
                break
    open(os.path.join(O, 'frac.tex'), 'w').write(t_frac())
    # Var(u) table
    vr = list(csv.DictReader(open(os.path.join(D, 'var_u.csv'))))
    t = ['\\begin{tabular}{rrrrrr}', '\\toprule', '$L$ & $M$ & 평균 $u$ & $\\mathrm{Var}(u)$ & $g_L(1)/M$ & 쌍 부등식 최소비\\\\', '\\midrule']
    for r in vr:
        mr = r['min_ratio_lhs_rhs']; mr = '--' if mr in ('', 'nan') else f"{float(mr):.3f}"
        t.append(f"{int(r['L'])} & {int(r['M'])} & {float(r['mean_u']):.5f} & {float(r['var_u']):.5f} & {float(r['f1_over_M']):.5f} & {mr}\\\\")
    t += ['\\bottomrule', '\\end{tabular}']
    open(os.path.join(O, 'var.tex'), 'w').write('\n'.join(t))
    print(open(os.path.join(O, 'H.tex')).read())
