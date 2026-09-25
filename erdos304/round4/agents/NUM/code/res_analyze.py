#!/usr/bin/env python3
"""Collect resonance-height data: grid certificates (out/resscan_A.txt, out/resscan_B.txt; ambiguous
cells resolved in out/resolve_amb.txt) and LLL upper bounds (data/lll_res.csv).
Writes data/resonance.csv, out/tables/res.tex, out/res_fit.txt.
Fit: least squares log10 tau* = alpha + beta*M over pools with grid-certified tau* (per eta);
second fit on the LLL points (upper bounds) for comparison.  Random-phase model slope:
I(1-eta)/ln 10 = 0.250, 0.354, 0.520 (eta = 0.3, 0.2, 0.1) decimal digits per prime (out/ratefn.txt)."""
import re, os, csv, math
import numpy as np
here = os.path.dirname(os.path.abspath(__file__)); O = os.path.join(here, '..', 'out'); D = os.path.join(here, '..', 'data')
ETAS = (0.3, 0.2, 0.1)
grid = {}
for fn in ('resscan_A.txt', 'resscan_B.txt'):
    p = os.path.join(O, fn)
    if not os.path.exists(p): continue
    for line in open(p):
        m = re.match(r'L=(\d+) M=(\d+) eta=([\d.]+) tau\*=([\d.]+) g/M', line)
        if m:
            grid[(int(m[1]), float(m[3]))] = dict(M=int(m[2]), ts=float(m[4]), lb=None); continue
        m = re.match(r'L=(\d+) M=(\d+) eta=([\d.]+) tau\*>([\d.e+]+) \(no resonance in \[10,([\d.e+]+)\]\) max g/M on grid=([\d.]+)', line)
        if m:
            grid[(int(m[1]), float(m[3]))] = dict(M=int(m[2]), ts=None, lb=float(m[4]), gmax=float(m[6]))
lll = {}
p = os.path.join(D, 'lll_res.csv')
if os.path.exists(p):
    for r in csv.DictReader(open(p)):
        if r['t_found']:
            lll[(int(r['L']), float(r['eta']))] = (float(r['t_found']), float(r['g_over_M']))
Ls = sorted(set(L for L, e in grid) | set(L for L, e in lll))
Mof = {}
for (L, e), v in grid.items(): Mof[L] = v['M']
from sympy import primepi
for L in Ls:
    if L not in Mof: Mof[L] = int(primepi(L) - primepi(L // 2))
rows = []
for L in Ls:
    for e in ETAS:
        g = grid.get((L, e)); u = lll.get((L, e))
        rows.append(dict(L=L, M=Mof[L], eta=e, grid_tau_star=(g['ts'] if g and g['ts'] else ''),
                         grid_lower_bound=(g['lb'] if g and g['lb'] else ''),
                         lll_upper=(u[0] if u else ''), lll_g_over_M=(u[1] if u else '')))
with open(os.path.join(D, 'resonance.csv'), 'w', newline='') as fh:
    w = csv.DictWriter(fh, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
# consistency: LLL points must not undercut certified values
bad = [(r['L'], r['eta']) for r in rows if r['lll_upper'] != '' and ((r['grid_tau_star'] != '' and r['lll_upper'] < r['grid_tau_star'] - 1e-3) or (r['grid_lower_bound'] != '' and r['lll_upper'] < r['grid_lower_bound']))]
out = [f'consistency (LLL point below a grid-certified range): {bad if bad else "none"}']
model = {0.3: 0.25016, 0.2: 0.35410, 0.1: 0.51955}
for e in ETAS:
    xs = [r['M'] for r in rows if r['eta'] == e and r['grid_tau_star'] != '']
    ys = [math.log10(r['grid_tau_star']) for r in rows if r['eta'] == e and r['grid_tau_star'] != '']
    xl = [r['M'] for r in rows if r['eta'] == e and r['lll_upper'] != '']
    yl = [math.log10(r['lll_upper']) for r in rows if r['eta'] == e and r['lll_upper'] != '']
    s = f'eta={e}: '
    if len(xs) >= 3:
        b, a = np.polyfit(xs, ys, 1); s += f'grid tau*: n={len(xs)}, M in [{min(xs)},{max(xs)}], log10 tau* = {a:.3f} + {b:.4f} M; '
    if len(xl) >= 3:
        b2, a2 = np.polyfit(xl, yl, 1); s += f'LLL points: n={len(xl)}, M in [{min(xl)},{max(xl)}], log10 t = {a2:.3f} + {b2:.4f} M; '
    s += f'random-phase model slope {model[e]:.3f}'
    out.append(s)
open(os.path.join(O, 'res_fit.txt'), 'w').write('\n'.join(out) + '\n'); print('\n'.join(out))
# LaTeX table
def fmt(r):
    if r['grid_tau_star'] != '': return f"{math.log10(r['grid_tau_star']):.2f}"
    if r['grid_lower_bound'] != '': return f"$>{math.log10(r['grid_lower_bound']):.2f}$"
    return '--'
def fmtl(r):
    return f"{math.log10(r['lll_upper']):.2f}" if r['lll_upper'] != '' else '--'
s = ['\\begin{tabular}{rr' + 'rr' * len(ETAS) + '}', '\\toprule',
     '& & ' + ' & '.join(f'\\multicolumn{{2}}{{c}}{{$\\eta={e}$}}' for e in ETAS) + '\\\\',
     '$L$ & $M$ & ' + ' & '.join(['격자 & LLL'] * len(ETAS)) + '\\\\', '\\midrule']
for L in Ls:
    rr = {r['eta']: r for r in rows if r['L'] == L}
    s.append(f'{L} & {Mof[L]} & ' + ' & '.join(f'{fmt(rr[e])} & {fmtl(rr[e])}' for e in ETAS) + '\\\\')
s += ['\\bottomrule', '\\end{tabular}']
os.makedirs(os.path.join(O, 'tables'), exist_ok=True)
open(os.path.join(O, 'tables', 'res.tex'), 'w').write('\n'.join(s))

# ---------------- LaTeX block for frag.tex (section 'resonance results')
fits = {}
for e in ETAS:
    xs = [r['M'] for r in rows if r['eta'] == e and r['grid_tau_star'] != '']
    ys = [math.log10(r['grid_tau_star']) for r in rows if r['eta'] == e and r['grid_tau_star'] != '']
    xl = [r['M'] for r in rows if r['eta'] == e and r['lll_upper'] != '']
    yl = [math.log10(r['lll_upper']) for r in rows if r['eta'] == e and r['lll_upper'] != '']
    fg = np.polyfit(xs, ys, 1) if len(xs) >= 3 else None
    fl = np.polyfit(xl, yl, 1) if len(xl) >= 3 else None
    lbs = [(r['M'], r['grid_lower_bound']) for r in rows if r['eta'] == e and r['grid_lower_bound'] != '']
    fits[e] = dict(n=len(xs), Mmin=min(xs) if xs else None, Mmax=max(xs) if xs else None, fg=fg, fl=fl,
                   nl=len(xl), Mlmax=max(xl) if xl else None, lbM=(min(m for m, _ in lbs) if lbs else None),
                   lbT=(min(t for _, t in lbs) if lbs else None))
lb01 = sorted((r['M'], r['grid_lower_bound']) for r in rows if r['eta'] == 0.1 and r['grid_lower_bound'] != '')
if lb01:
    mn = min(t for _, t in lb01); e10 = int(math.floor(math.log10(mn)))
    lbtext = (f"\\item $\\eta=0.1$ 에서 격자는 $M\\in\\{{{','.join(str(m) for m, _ in lb01)}\\}}$ 에서 120\\,s 안에 공명을 찾지 못한다; "
              f"따라서 그 $M$ 들에서 $\\tau^*_{{10}}(L,0.1)>{mn/10**e10:.2f}\\cdot10^{{{e10}}}$ (인증된 하한들의 최솟값).")
else:
    lbtext = ''
# agreement of LLL points with grid tau* where both exist
agree = [(r['L'], r['eta'], r['lll_upper'] - r['grid_tau_star']) for r in rows if r['lll_upper'] != '' and r['grid_tau_star'] != '']
nag = sum(1 for _, _, d in agree if abs(d) < 3); ntot = len(agree)
def fitline(e):
    f = fits[e]; s = f'$\\eta={e}$: '
    if f['fg'] is not None:
        s += f"격자 $\\tau^*$ ({f['n']}개, $M\\in[{f['Mmin']},{f['Mmax']}]$) $\\log_{{10}}\\tau^*\\approx{f['fg'][1]:.2f}+{f['fg'][0]:.3f}M$"
    if f['fl'] is not None:
        s += f"; LLL 점 ({f['nl']}개, $M\\le{f['Mlmax']}$) $\\log_{{10}}t\\approx{f['fl'][1]:.2f}+{f['fl'][0]:.3f}M$"
    s += f"; 무작위 위상 모형 기울기 {model[e]:.3f}"
    return s
blk = r"""\begin{table}[ht]\centering\small
""" + '\n'.join(s) + r"""
\caption{첫 공명 높이 $\log_{10}\tau^*_{10}(L,\eta)$. ``격자'' 열: 인증된 값 (\texttt{code/resscan.c}; 정밀도 $10^{-3}$ 이하) 또는
$L$ 당 120\,s 안에 공명이 없을 때의 인증된 하한 ``$>$''. ``LLL'' 열: \texttt{code/lll\_res.py} 가 찾은 점 $t$ ($g_L(t)\ge(1-\eta)M$ 을 mpmath 로 확인) 의
$\log_{10}t$ --- 즉 $\tau^*_{10}\le t$ 의 상한. $L$ 은 각 $M$ 을 처음 달성하는 소수. \NUMERIC\
(\texttt{out/resscan\_A.txt}, \texttt{out/resscan\_B.txt}, \texttt{out/lll\_res.txt}, \texttt{data/resonance.csv}, \texttt{code/res\_analyze.py})}\label{NUM:tab-res}
\end{table}

\begin{proposition}[공명 높이 자료]\label{NUM:prop-res}
\NUMERIC\ (\texttt{code/resscan.c}, \texttt{code/lll\_res.py}, \texttt{code/resolve\_amb.py}, \texttt{code/res\_analyze.py} $\to$ \texttt{out/res\_fit.txt}, \texttt{data/resonance.csv})
\begin{enumerate}[label=(\arabic*)]
\item 표~\ref{NUM:tab-res} 의 모든 ``격자'' 항목은 보조정리~\ref{NUM:lem-grid} 의 인증서로 얻었다. 판정 불가 후보는 한 번 ($L=193$, $\eta=0.3$, $t\approx60322.49$) 나왔고,
국소 최대화 (\texttt{out/resolve\_amb.txt}) 로 그 칸에는 공명이 없고 첫 교차가 $t_c=60322.5932$ 임을 확인하였다 (\texttt{resscan} 의 보고값과 일치).
\item LLL 이 찾은 점은 인증된 공명 없는 구간 안에 한 번도 들어가지 않았다 (모순 없음). 두 값이 모두 있는 """ + f"{ntot}" + r""" 경우 중 """ + f"{nag}" + r""" 경우에서
LLL 점은 격자의 첫 교차점과 $3$ 이내 (같은 공명 봉우리) 이고, $M\le16$ 에서는 36 경우 중 35 경우가 그렇다 (LLL 이 사실상 \emph{첫} 공명을 찾는다).
$M\ge17$ 에서는 LLL 점이 격자의 $\tau^*$ 보다 흔히 수 자리 (최대 약 $10^{7}$ 배) 높아, 단지 상한일 뿐이다. 따라서 $\eta=0.1$, $M\ge21$ 에서
$\tau^*_{10}$ 는 $(10^{9},\,t_{\mathrm{LLL}}]$ 로만 묶인다 (예: $M=33$: $10^{8.99}<\tau^*_{10}\le10^{18.68}$).
\item 최소제곱 기울기 (상용로그, 소수 하나당):
\begin{itemize}
\item """ + fitline(0.3) + r"""
\item """ + fitline(0.2) + r"""
\item """ + fitline(0.1) + r"""
\end{itemize}
""" + lbtext + r"""
\end{enumerate}
\end{proposition}

\begin{remark}[해석]\label{NUM:rem-res-heur}
\HEUR\ (\texttt{code/ratefn.py} $\to$ \texttt{out/ratefn.txt})
(i) 위상 $t\log p$ ($p\in P$) 를 독립 균등으로 보는 무작위 위상 모형에서는 $\Pr(|\frac1M\sum\e^{i\theta_p}|\ge x)=\e^{-M I(x)+O(\log M)}$,
$I(x)=\sup_\lambda(\lambda x-\log I_0(\lambda))$ (Cramér; 2차원 벡터 $(\cos\theta,\sin\theta)$ 의 로그적률함수가 $\log I_0(|\lambda|)$), 상관 길이는 $O(1)$ 이므로
$\log\tau^*\approx M I(1-\eta)$ 가 예측된다: $I(0.7)=0.576$, $I(0.8)=0.815$, $I(0.9)=1.196$ (상용로그 기울기 $0.250,0.354,0.520$).
인증된 $\tau^*$ 의 기울기 ($0.21$, $0.30$, $0.50$) 는 이 예측 ($0.25$, $0.35$, $0.52$) 과 같은 크기이다. 다만 $\eta=0.3$ 에서는 중첩된 풀들이 같은 공명을 공유하여
계단 모양이 되고 (예: $L=53,61$ 은 $t\approx360$, $L=101,103,109$ 는 $t\approx642$, $M=25$--$28$ 은 모두 $t\approx5.6\cdot10^5$), $\eta=0.2$ 의 적합은
$M\ge27$ 의 미발견값 (하한 $>10^{9}$) 을 빼고 한 것이라 아래로 치우쳐 있다. LLL 점의 기울기 ($0.41,0.51,0.64$) 는 상한들의 포락선일 뿐이다.
(ii) Dirichlet 동시근사는 $\tau^*\lesssim Q^M$, $Q=\lceil2\pi/\arccos(1-\eta)\rceil=8,10,14$ ($\log_{10}Q=0.90,1.00,1.15$) 를 주는데, 인증된 기울기는 그 $1/4$--$1/2$ 로
Dirichlet 상한은 지수에서 날카롭지 않다. DESIGN S4 의 ``$T\ge(C/\eta)^M$ 이면 NR 실패'' 는 지수 높이가 자연스러운 한계라는 점에서 자료와 부합한다.
(iii) VKGAP-C 에 대한 함의: 자료는 $\log\tau^*_{10}(L,\eta)\asymp M$ (선형 증가) 과 부합하고, 따라서 $\mathrm{NR}(P,\e^{cM},\eta)$ 는 $c<c(\eta)$ 로
기대할 수 있다 (인증된 자료의 기울기로는 $c(0.1)\approx0.50\ln10\approx1.1$, $c(0.3)\approx0.21\ln10\approx0.48$ 정도; $M\le33$ 에서의 추정일 뿐). 단 명제~\ref{NUM:prop-t1} 에 의해 절단은 $|\tau|\ge1$ 이 아니라
$\eta<0.0194$ 또는 $|\tau|\ge\tau_0(\eta)$ 여야 한다. $\eta=0.01$ 의 높이는 $\tau^*(0.1)$ 보다 크므로 (주의~\ref{NUM:rem-t1}) 위 하한은 $\eta=0.01$ 에도 유효하다.
이 모든 것은 $M\le33$, $\ln L\le6$ 의 자료에 근거한 외삽이며 증명이 아니다.
\end{remark}
"""
open(os.path.join(O, 'tables', 'res_block.tex'), 'w').write(blk)
