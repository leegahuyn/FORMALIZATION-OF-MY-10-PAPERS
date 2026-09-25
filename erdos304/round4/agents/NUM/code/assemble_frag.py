#!/usr/bin/env python3
"""Assemble agents/NUM/frag.tex from frag_src.tex + generated tables (out/tables/) + blocks below.
Run make_tables.py and res_analyze.py first."""
import os, re, csv
here = os.path.dirname(os.path.abspath(__file__)); B = os.path.join(here, '..')
T = lambda n: open(os.path.join(B, 'out', 'tables', n)).read()
src = open(os.path.join(B, 'frag_src.tex')).read()

def mitm_text():
    s = open(os.path.join(B, 'out', 'mitm23.txt')).read()
    n3 = re.search(r'\|S3\| by triple enumeration = (\d+)', s)[1]
    dif = re.search(r'S3 vs checkpoint R_3: (\d+) differing', s)[1]
    m = re.search(r'samples: (\d+) with BFS kappa=7 \(no MITM witness expected\), (\d+) with kappa<=6; disagreements: (\d+)', s)
    return (f"세 약수 합을 직접 나열한 $S_3=\\{{d_1+d_2+d_3<\\Lam: d_i\\in D^*\\cup\\{{0\\}}\\}}$ 는 $|S_3|={n3}$ 이고 BFS 의 $R_3$ 와 "
            f"비트 단위로 같다 (다른 비트 {dif}개). $\\kappa(a)\\le6\\iff a\\in S_3+S_3$ 를 전수 대조하여 $a_7=3\\,716\\,552\\,837$ 이 $S_3+S_3$ 에 "
            f"없음 (즉 $\\kappa(a_7)\\ge7$) 을 BFS 와 독립으로 확인하였고, $a_7$ 과 표본 40개 (20개는 BFS 가 $\\kappa=7$ 로 판정한 수에서, 20개는 균등 무작위; 합계 $\\kappa=7$ 판정 {m[1]}개 --- 일부는 $a_7$ 과 겹침 --- , $\\kappa\\le6$ 판정 {m[2]}개) 에서 "
            f"BFS 의 $R_6$ 판정과 불일치 {m[3]}개.")

def dyad(L):
    s = open(os.path.join(B, 'out', 'tables', f'dyadic{L}.txt')).read().strip()
    parts = []
    for item in s.split('; '):
        m = re.match(r'j=(\d+)\.\.(\d+): (\d+)', item)
        a, b, k = m[1], m[2], m[3]
        parts.append((f'$j={a}$' if a == b else f'$j={a}$--${b}$') + f' 에서 ${k}$')
    return ', '.join(parts)

def l25_complete():
    for pre in ('hbfs_L25', 'hbfs2_L25'):
        p = os.path.join(B, 'data', 'bfs', pre + '_levels.csv')
        if os.path.exists(p):
            r = list(csv.DictReader(open(p)))
            if r and int(r[-1]['ones_Rk']) == int(r[-1]['Lambda']): yield pre, r

def l25_block():
    got = dict(l25_complete())
    if 'hbfs2_L25' not in got: return '% L=25 not finished\n'
    r = got['hbfs2_L25']
    same = ''
    if 'hbfs_L25' in got:
        a = [x[:10] for x in csv.reader(open(os.path.join(B, 'data', 'bfs', 'hbfs_L25_levels.csv')))]
        b = [x[:10] for x in csv.reader(open(os.path.join(B, 'data', 'bfs', 'hbfs2_L25_levels.csv')))]
        da = [x for x in csv.reader(open(os.path.join(B, 'data', 'bfs', 'hbfs_L25_dyadic.csv')))][1:]
        db = [x for x in csv.reader(open(os.path.join(B, 'data', 'bfs', 'hbfs2_L25_dyadic.csv')))][1:]
        ok = (a == b) and (da == db)
        same = ('두 번째 구현 \\texttt{hbfs} (두 비트집합, 6.7\\,GB; \\texttt{out/hbfs\\_L25.log}, \\texttt{data/bfs/hbfs\\_L25\\_*.csv}) 으로 다시 계산한 단계별 표와 이진 척도 표가 '
                + ('완전히 일치한다.' if ok else '\\textbf{일치하지 않는다} (조사 필요).'))
    else:
        same = '두 번째 구현 \\texttt{hbfs} 에 의한 재계산은 끝나지 않았다 (\\texttt{out/hbfs\\_L25.log} 참조).'
    return r"""\subsection{결과: $H(25)=H(26)=8$}\label{NUM:ssec-H25}

\begin{theorem}[수치 결과]\label{NUM:thm-H25}
\NUMERIC\ (\texttt{code/hbfs2.c}; \texttt{out/hbfs2\_L25.log}; \texttt{data/bfs/hbfs2\_L25\_levels.csv}, \texttt{data/bfs/hbfs2\_L25\_dyadic.csv};
$\kappa=8$ 목록 \texttt{code/extract\_top.py} $\to$ \texttt{data/L25\_kappa8.csv}, \texttt{out/extract\_top\_L25.txt};
표현 \texttt{code/repr\_dfs.py} $\to$ \texttt{out/repr\_L25.txt})
$\Lam_{25}=\Lam_{26}=26\,771\,144\,400$, $\tau=2880$ 에 대하여 $H(25)=H(26)=8$ 이다.
\begin{enumerate}[label=(\arabic*)]
\item 단계별 자료는 표~\ref{NUM:tab-L25}. $\#\{a:\kappa(a)=8\}=1\,158$ (비율 $4.3\cdot10^{-8}$) 뿐이다.
\item $a_c$ ($c=1,\dots,8$) $=1,\ 27,\ 10\,103,\ 5\,959\,627,\ 381\,174\,281,\ 3\,805\,051\,219,\ 13\,192\,321\,591,\ 26\,577\,893\,791$.
\item $Z^-_6=1\,158$, $Z^-_7=0$ 이므로 $\max_{a<\Lam/2}\kappa(a)=7$, $H(25)=1+\max_{a<\Lam/2}\kappa(a)$; $\kappa=8$ 인 $a$ 는 모두 $[\Lam/2,\Lam)$ 에 있다.
또 모든 $k\ge1$ 에서 $Z^+_k=Z^-_{k-1}$ 이므로 (보조정리~\ref{NUM:lem-shift}) 모든 $b<\Lam_{25}/2$ 에서 $\kappa(\Lam/2+b)=1+\kappa(b)$.
\item 최적 표현 (모두 서로 다른 약수; 합·약수성 검증; $\kappa(a_8)\ge8$ 은 BFS 의 $a_8\notin R_7$):
\[
a_8=26\,577\,893\,791=\tfrac{\Lam}{2}+\tfrac{\Lam}{3}+\tfrac{\Lam}{7}+\tfrac{\Lam}{63}+\tfrac{\Lam}{1400}+\tfrac{\Lam}{278\,460}+\tfrac{\Lam}{66\,927\,861}+\tfrac{\Lam}{5\,354\,228\,880}
\]
$=13385572200+8923714800+3824449200+424938800+19122246+96140+400+5$; $a_7$ 은 첫 항을 뺀 7항.
(표현 탐색: 큰 항은 깊이우선 탐색, 나머지 $r<2^{30}$ 은 BFS 가 함께 저장한 $\kappa(r)$ 표로 Bellman 역추적. $\kappa(r)$ 표는 $L=23$ 에서 체크포인트 $R_k$ 와 $[0,2^{30})$ 전체가 일치함을 확인.)
\item $\kappa=8$ 인 $1158$ 개는 $\Lam$ 바로 아래에 몰려 있다: $a/\Lam\ge0.99278$, 중앙값 $0.99996$;
$\Lam-a<10^3$ 인 것이 8개 ($\Lam-a=223,293,307,337,397,433,491,883$, 모두 소수), $\Lam-a<10^6$ 인 것이 586개; $1158$ 개 중 $1095$ 개에서 $\Lam-a$ 는 $\Lam$ 과 서로소이다.
\item 이진 척도별 최대 $\kappa$: """ + dyad(25) + r""".
\item 실행: \texttt{hbfs2} 2 스레드 609\,s, 메모리 4.4\,GB. """ + same + r"""
\end{enumerate}
\end{theorem}

\begin{table}[ht]\centering\small
""" + T('levels25.tex') + r"""
\caption{$L=25$ ($\Lam=26\,771\,144\,400$): BFS 단계별 자료 (표~\ref{NUM:tab-L23} 과 같은 기호). \NUMERIC\ (\texttt{data/bfs/hbfs2\_L25\_levels.csv})}\label{NUM:tab-L25}
\end{table}

\begin{remark}\label{NUM:rem-H25}
\HEUR\ $H$ 가 처음으로 $k$ 가 되는 $L$ 은 $k=1,\dots,8$ 에 대해 $2,3,4,5,7,11,17,25$ 이다. $L=25$ 에서의 증가는 소수거듭제곱 $5^2$ 에서 일어나며
($\tau$ 는 $1.5$ 배만 증가), $\kappa=8$ 인 수가 $4.3\cdot10^{-8}$ 비율밖에 없어 ``아슬아슬한'' 증가이다. $H/\ln L$ 은 $L=25$ 에서 $2.49$, $L=26$ 에서 $2.46$ 으로
$L\le22$ 의 범위 $[2.16,2.57]$ 안에 있다.
\end{remark}
"""

def summary_rows():
    rows = [
        ('중복 제거 $\\Rightarrow$ $\\kappa(a)=\\min\\{k:a\\in R_k\\}$, $H=\\min\\{k:R_k=[0,\\Lam)\\}$', '\\PROVED', '명제~\\ref{NUM:prop-bfs}'),
        ('$a_c=\\min([0,\\Lam)\\setminus R_{c-1})$; $\\kappa(\\Lam/2+b)\\le1+\\kappa(b)$', '\\PROVED', '보조정리~\\ref{NUM:lem-ac}'),
        ('이동 항등식 $\\iff$ $Z^+_k=Z^-_{k-1}$ ($\\forall k$)', '\\PROVED', '보조정리~\\ref{NUM:lem-shift}'),
        ('$L\\le22$: p1p4 표 5--7 재현 (불일치 0); $\\kappa$ 배열 전체가 0/1 DP 와 일치 ($L\\le19$, 따라서 $L\\le22$) --- 중복 제거 정리의 수치 확인', '\\NUMERIC', '명제~\\ref{NUM:prop-valid}'),
        ('$H(23)=H(24)=7$, $\\#\\{\\kappa=7\\}=167\\,987\\,582$, $a_7=3\\,716\\,552\\,837$ (7항 표현)', '\\NUMERIC', '정리~\\ref{NUM:thm-H23}'),
        ('$H(25)=H(26)=8$, $\\#\\{\\kappa=8\\}=1\\,158$, $a_8=26\\,577\\,893\\,791$ (8항 표현)', '\\NUMERIC', '정리~\\ref{NUM:thm-H25}'),
        ('$L\\le26$ 모두에서 $H=1+\\max_{a<\\Lam/2}\\kappa$ 이고 $\\kappa(\\Lam/2+b)=1+\\kappa(b)$ ($\\forall b$)', '\\NUMERIC', '정리~\\ref{NUM:thm-H23}, \\ref{NUM:thm-H25}'),
        ('이동 항등식의 일반 $L$ 증명', '\\OPEN', '주의~\\ref{NUM:rem-H-trend}'),
        ('$g_L(1)/M\\to|F(1)|=0.98057$; $\\eta>0.0195$ 이면 $\\mathrm{NR}(P,T,\\eta)$ (절단 $|\\tau|\\ge1$) 는 큰 $L$ 에서 거짓', '\\PROVED\\ (\\EXT\\ PNT)', '명제~\\ref{NUM:prop-t1}'),
        ('격자 인증서 (립시츠 상수 $K\\le\\frac{\\ln2}{2}M$)', '\\PROVED', '보조정리~\\ref{NUM:lem-grid}'),
        ('공명 높이 $\\tau^*_{10}(L,\\eta)$ 표와 기울기', '\\NUMERIC', '표~\\ref{NUM:tab-res}'),
        ('$\\log\\tau^*\\asymp M$ 의 점근 및 무작위 위상 모형 기울기 $I(1-\\eta)$', '\\HEUR', '주의~\\ref{NUM:rem-res-heur}'),
        ('$\\sup_{|t|\\ge1}|F(t)|=|F(1)|=0.980572<0.99$', '\\NUMERIC', '명제~\\ref{NUM:prop-F}'),
        ('$\\mathrm{Var}(u)\\to0.039094$ (밀도 $2\\e^{-u}$), 유한 $L$ 값, 쌍 부등식', '\\PROVED\\ (\\EXT)/\\NUMERIC', '명제~\\ref{NUM:prop-var}'),
    ]
    return '\n'.join(f'{a} & {b} & {c}\\\\' for a, b, c in rows)

res_block = open(os.path.join(B, 'out', 'tables', 'res_block.tex')).read() if os.path.exists(os.path.join(B, 'out', 'tables', 'res_block.tex')) else '% resonance block pending\n'
Hlast = '26' if any(True for _ in l25_complete()) else '24'
rep = {
    '%%MITM%%': mitm_text(),
    '%%DYAD23%%': dyad(23),
    '%%LEVELS23%%': T('levels23.tex'),
    '%%L25BLOCK%%': l25_block(),
    '%%HTABLE%%': T('H.tex'),
    '%%LMAX%%': Hlast,
    '%%FRACTABLE%%': T('frac.tex'),
    '%%HLAST%%': '24',
    '%%SHIFTL%%': Hlast,
    '%%RESBLOCK%%': res_block,
    '%%VARTABLE%%': T('var.tex'),
    '%%SUMMARYROWS%%': summary_rows(),
}
for k, v in rep.items():
    src = src.replace(k, v)
assert '%%' not in src, re.findall(r'%%\w+%%', src)
open(os.path.join(B, 'frag.tex'), 'w').write(src)
print('frag.tex written', len(src), 'chars')
