# BRIEF — Erdős–Graham #304, Round 4 (read this first)

Campaign root: `/home/user/FORMALIZATION-OF-MY-10-PAPERS/erdos304/round4` (call it `$R`).
Lead: main session. Date: 2026-09-25. Language of deliverables: **Korean** prose, standard math notation.

## 0. Honesty contract (non-negotiable)

Every statement you write carries exactly one tag:
- `\PROVED` — complete argument written out in your fragment (no "clearly", no "standard" for non-textbook steps);
- `\COND{X}` — rigorous implication from a named hypothesis X;
- `\REFUTED` — counterexample or impossibility proof given;
- `\NUMERIC` — computed; give the script path (`$R/agents/<ID>/code/...`) and output path;
- `\HEUR` — reasoning only;
- `\OPEN` — not proved.
- `\EXT` — a cited external theorem used as a black box (state it precisely; say whether you verified the statement from a source or it is "recalled, unverified").

Rules:
- **Erdős #304 is OPEN** (web search 2026-09-25: best upper bound Vose `N(b) ≪ sqrt(log b)`; lower bound Erdős `≫ log log b`). Do not claim to solve it. Never upgrade a tag without a complete proof.
- Network: arXiv, erdosproblems.com and most journal sites are **blocked**. Only `WebSearch` (snippets) works. If you use a literature statement, write "snippet-verified" (you saw the statement in a search snippet) or "recalled, unverified". Textbook facts (PNT with error term, Siegel–Walfisz, Vinogradov–Korobov zero-free region, Gauss sums, Beurling–Selberg majorant/minorant, Fejér kernel, Chebyshev bounds) may be used as `\EXT` with a precise statement and a textbook reference (e.g. Montgomery–Vaughan *Multiplicative Number Theory I*; Titchmarsh *Theory of the Riemann zeta-function* §6.19; Ivić *The Riemann zeta-function* Thm 6.1; Iwaniec–Kowalski).
- Precise obstructions, counterexamples and conditional theorems are valuable. An over-claimed proof is worthless and will be caught by the auditors.

## 1. Problem and notation

- `N(a,b)` = least `k` with `a/b = 1/n_1+...+1/n_k`, `n_i` distinct; `N(b)=max_{1≤a<b} N(a,b)`. Conjecture (#304): `N(b) ≪ log log b`.
- `Λ = Λ_L = lcm(1,...,L)`, `log Λ_L = ψ(L) = (1+o(1))L`. `a_p = floor(log L/log p)` so `Λ_L = ∏ p^{a_p}`. `D*_L` = proper divisors of `Λ_L`.
- `g_L(a)` = least number of **distinct** proper divisors of `Λ_L` summing to `a` (`g_L(0)=0`); `H(L) = max_{0≤a<Λ_L} g_L(a)` (= `h(Λ_L)`).
- Pool: `P = {p prime : L/2 < p ≤ L}`, `M = |P| ~ L/(2 log L)`, each `p∈P` has `a_p=1`. `Q = Λ_L/∏_{p∈P} p`; every divisor is uniquely `c·U(E)`, `c | Q`, `E ⊆ P`, `U(E)=∏_{p∈E} p`.

## 2. What is already PROVED (import freely, cite by pointer)

Corpus files (text extracted from the user's two PDFs):
- `$R/corpus/baker_0925.txt` — "Erdős–Graham 304 연구기록, Baker–Matveev", 2026-09-25 (74 pp.).
- `$R/corpus/p1p4_0924.txt` — "P1–P4 증명 캠페인 최종 보고서", 2026-09-24 (76 pp.).

| Fact | Status | Pointer |
|---|---|---|
| Transfer: `b ≤ Λ_L ⇒ N(a,b) ≤ 2H(L)`; `H(L) ≪ log L ⇒ N(b) ≪ log log b` | PROVED | p1p4 5752–5819; baker 252–284 |
| **Dedup theorem**: min #terms with repetition allowed = min with distinct terms, for all `0≤a<Λ_L` (least-deficient-prime swap `d+d → pd/r + d/r`, `r=(p+1)/2`, or `d+d→2d`) | PROVED (baker) — re-verify | baker 461–499 |
| Bellman: `g(a)=1+min_{d≤a} g(a-d)`; `[z^a](1+Σ_{d∈D*} z^d)^k>0 ⇔ g(a)≤k` | PROVED | baker 503–528 |
| Mixed radix `H(L) ≤ π*(L) ~ L/log L` | PROVED | p1p4 1636–1680 |
| Entropy lower bound `H(L) ≥ (1/log 2 − o(1)) log L` | PROVED | baker 316–352; p1p4 5931 |
| Consecutive divisors of `Λ_L` have ratio ≤ 2 | PROVED | p1p4 1604–1633 |
| Small residues avoiding a used set `U`: `2u+3 ≤ R < min((L/2)^{k+1},Λ)` is a sum of ≤ k+2 distinct divisors avoiding `U` if `M ≥ (3u+3)k+u+1` | PROVED | p1p4 1688–1740 |
| Greedy barrier: greedy needs `≥(1−o(1)) log L log log L` steps for some `a` | PROVED | p1p4 1808–1979 |
| Gap hypothesis ⇒ bound: `GH(δ,X0)` (every `x∈[X0,Λ/X0]` has a divisor in `[(1−δ)x,x]`) ⇒ `H(L) ≤ log_2 X0 + log Λ/log(1/δ) + log X0/log(L/2) + 5` | PROVED | p1p4 1980–1993 |
| Char. function of n-subset log-sums: `|E e^{iτS}| ≤ 3√n exp(−q(1−q)(M − |Σ_{p∈P} p^{iτ}|))` | PROVED | p1p4 2000–2050 |
| Cascade assembly theorem, SP1 ⇒ `H ≪ log L` | PROVED/COND | p1p4 5827–6030 |
| Banding counting lower bounds (dyadic bands lose `log log`) | PROVED | p1p4 6418–6503 |
| Shared resonance at prime moduli `a/p`, `3≤p≤L/2` (Thm 4.19) | PROVED | p1p4 970–1085 |
| Composite-modulus mixing (CMM) | **OPEN** (next goal #1) | p1p4 1157–1181, 7727–7730 |
| RC ⇒ top-zone stage P1 | PROVED (implication) | p1p4 1341–1463 |
| Smooth-number transfer: every `n∈[L, e^{L^δ}]` is a sum of 4 distinct proper divisors (via Drappeau–Shao + Harper) and bundled mixed radix `H(L) ≪ L^{1−δ}` | COND on literature (baker) — re-verify | baker 1794–2027 |
| Hughes (arXiv:2609.10902, snippet-verified): `h(n!) ≤ (2log2+o(1)) n/log n` ⇒ `N(b) ≤ (4log2+o(1)) log b/(log log b)^2` | EXT | p1p4 7399–7427 |
| Baker–Matveev in full dimension is weaker than trivial integer spacing | PROVED | baker 2794–2848 |
| Exact `H(L)` for `L ≤ 22`: 1,2,3,4,4,5,5,5,5,6,6,6,6,6,6,7,7,7,7,7,7 | NUMERICAL | p1p4 6678–6773 |

**The single remaining core** (SP1, equivalently): `H(L) ≪ log L` — OPEN. It would imply Erdős #18 Q1 (`h(m) < (log log m)^{O(1)}` for infinitely many practical `m`, a $250 open problem) in strong form.

## 3. Compute limits

Machine: 4 cores, 15 GB RAM, shared by all agents. Use `nice -n 10`. Ordinary jobs < 5 min. Only the NUM agent may run one long job (≤ 45 min wall, ≤ 7 GB RAM, ≤ 2 threads) and must checkpoint. Python has numpy/sympy/mpmath; gcc available.

## 4. Output conventions (write incrementally — you may be cut off)

Your directory: `$R/agents/<ID>/` containing
- `frag.tex` — LaTeX body starting with `\section{...}` (Korean), all labels prefixed `<ID>:` (e.g. `\label{VKGAP:thm-main}`), using only macros from `$R/tex/preamble.tex` (tags `\PROVED \COND{..} \OPEN \REFUTED \NUMERIC \HEUR \EXT`, environments `theorem lemma proposition corollary conjecture hypothesis definition example counterexample remark`, `proof`). No `\documentclass`, no `\begin{document}`.
- `summary.md` — results with tags, key numbers, file paths; update it as you go.
- `code/` and `out/` for scripts and outputs.
- Compile-test: `$R/tex/test_frag.sh $R/agents/<ID>/frag.tex` must print `COMPILE OK`.
- Save to disk after every substantial step. Final chat message: ≤ 25 lines: results with tags, key numbers, paths.

Read `$R/DESIGN.md` next.
