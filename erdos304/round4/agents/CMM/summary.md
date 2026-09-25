# CMM — summary (written by the lead from the agent's final report; agents could not write .md files)

Fragment: `frag.tex` (573 lines, 10 pp., compile OK). Pending Stage-2 audit.

1. [PROVED] Exact expansion (Prop CMM:prop-exact), all q | Q incl. prime powers: µ(a/q) = M(q) + R, M(q) = ∏_j (v_j+1−k_j−1/(p_j−1))/(v_j+1) (squarefree, p_j ∈ (√L, L/2]: ∏(1/2 − 1/(2(p_j−1)))). Error ≤ B(S,m) = √d/φ(d) Σ_{χ prim mod d} |Eχ(c')|. Conjugates placed correctly (literal no-conjugate version refuted numerically). U(E) law arbitrary; q_j ∉ E always.
2. [PROVED] 2k-th moment: #{χ: Re A(χ) > (1−η)N_1} ≤ φ(d)(1−η)^{−2k} N_1^{−k} k! ((L/2)^k/d + 1); B ≤ √d e^{−ηN_1/4} + 2k! κ^k/√d, k = ⌈log d/log(L/2)⌉, κ ≤ 1.5 log L/(1−η)^2.
3. [PROVED, effective, no Siegel–Walfisz] Cor CMM:cor-large: squarefree q, p_j ∈ (√L, L/2], ωκ_* ≤ √(L/2): |µ(a/q)| ≤ ∏(1/2 + ε_j), ε_j = (1/(p_j−1) + β_L)/2, β_L ≪ L^{−1/4} log L log log L + (ω log L)^{1/2} L^{−1/4}; ε_L → 0 iff ω = o(√L/log L).
4. [PROVED, effective] Thm CMM:thm-asym: p_j ≥ y ≥ √L ⇒ |µ − M| ≤ 2^{−ω} e^{ω/(y−1)} (4ωκ_*/√y + η'_L); y = √L: relative error O(ω log L/L^{1/4}) for ω ≤ L^{1/4}/(2κ_*); y = L/3: upgrades p1p4 (T3) HEURISTIC → PROVED for h' ≤ c√L/log L.
5. Thm CMM:thm-main (general q | Q, 2ωκ_* ≤ √(L/2), ω up to L^{1/2−ε}): |µ| ≤ ∏ ρ_{p^k}; effective for p_j > (log L)^A; uses Siegel–Walfisz (EXT, ineffective) for small prime factors.
6. Thm CMM:thm-SS, s ≥ (2+δ) log_2 L: (a) [PROVED eff.] large primes, ω = o(√L/log L): Σ = 1 + O(L^{−δ/2}/log L); (b) [PROVED eff.] all p > (log L)^A, ω ≤ L^{1/2−ε}: 1 + o(1); (c) [PROVED via S–W] all q | Q, ω ≤ L^{1/2−ε}: O_ε(1), tail → 0. Upgrades p1p4 Rem 4.21, 4.27(2)(d) (Cor CMM:cor-upgrade).
7. Limits: [PROVED] moment-method barrier at x ≍ √L/log L; [PROVED] bad primitive characters exist once ω(q) > N_1 (F_2 linear algebra, quadratic characters). [OPEN] ω(q) > L^{1/2−ε} (includes all q ≥ R_*: the global problem Q·P(Y ≡ R mod Q)); asymptotic formula for L^{1/4}/log L ≲ ω ≲ √L/log L; effective small moduli; size-window variant. RC and SP1 untouched; #304 open.
8. [NUMERICAL] exact DP+FFT checks ω = 2,3, L = 60–2000, small primes and prime powers (3·7·11, 8·9·5): main term confirmed; true error below Prop-exact bound by factors 0.36–5.7e−5; no bad characters for L ≥ 300. Proved constants non-trivial only for L ≳ 10^12–10^16.

Files: code/cmm_exact.py → out/cmm_exact.txt; code/cmm_constants.py → out/cmm_constants.txt; code/check_local.py → out/check_local.txt.

## Stage-2 audit (AUD1): CONFIRMED 19, MINOR-FIX 6, GAP 0, WRONG 0
- Core mathematics confirmed (exact expansion incl. prime powers/2-powers, conjugates, moment count, multiplicative bound, asymptotic, effective claims avoid S–W except (H_Z-ii), SS(c), upgrade corollary; singular series; both barriers).
- Fixes (marked `% AUD1:` in frag.tex): (1) bad-character proposition true, but "cancellation between B(S) terms needed" does not follow; (2) new PROVED Parseval lower bound (AUD1 file): RHS of Prop exact ≥ 2^{−ω} q^{−1/2}(φ(q)/τ(Q') − 1), so the absolute-value expansion is useless once log q ≥ (log 2+o(1))L/log L; range √L/log L … L/(log L)^2 OPEN; (3) Remark 4.27(2)(d) upgrade only covers q ≤ L^{ω_0} ≪ R_*; q ≥ R_* stays OPEN; (4) Cor T3 needs c ≤ 0.156 (non-trivial for c < 0.078); SS(a) "effective" only with explicit o(·); "threshold unchanged" only for ω(q) ≤ ω_0; table #bad 225 → 224; missing 8·9·5 bounds filled.
- Numerics independently reproduced; conjugate formula error ≤ 8.5e−14 vs literal 1.90–2.00.
