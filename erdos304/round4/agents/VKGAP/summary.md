# VKGAP — summary (written by the lead from the agent's final report)

Fragment: `frag.tex` (12 pp., 43 labels `VKGAP:`, compile OK; ledger at §VKGAP:sec-ledger). Pending audit (AUD3).

- [PROVED] Cofactor lemma: divisors of Q_y = Λ_L/∏_{P_y} p (incl. Q) have consecutive ratio ≤ 2.
- **VKGAP-A** [COND on textbook inputs only: (E1) PNT, (E2) VK zero-free region (Titchmarsh 6.19 / Ivić 6.1 / IK 8.29, recalled), (E3) partial-fraction formula for ζ'/ζ (Titchmarsh 9.6(A), 9.2), (E4) Mellin inversion]: for L ≥ y_2 every x ∈ [X_0, Λ_L/X_0] has divisors of Λ_L in [(1−δ)x, x] and [x, (1+2δ)x], with δ = 8π exp(−(log L)^{3/2}(log log L)^{−3}), X_0 = exp(1.08·10^5 (log L)^3 log log L + 2). Design: lattice-resonant band τ_1 ≤ |τ| ≤ 4 enters only via ∫e^{−c_2 nτ^2}dτ (no factor T) ⇒ n ≥ C_0 (log L)^2 log log L suffices; trapezoid-weighted prime sum + Mellin contour shift (only the lower bound on Σ(1−cos) is needed); local CLT with explicit cumulant remainder (97/288)|τ|^3 b σ^2; upper local bound via Fejér; explicit constants, margin 0.375 vs 0.203.
- **VKGAP-B** [COND on textbook inputs]: H(L) ≤ (1+O((log log L)^3/(log L)^{3/2})) L (log log L)^3/(log L)^{3/2}; N(b) ≤ (2+o(1)) log b (log log log b)^3/(log log b)^{3/2}. Weaker than Hughes (log b/(log log b)^2) and far from Vose — stated in the frag.
- General transfer [COND on NR'(T',η)]: log(1/δ(ℓ)) ≥ min(log T' − 2, η D(ℓ)/(16 log L)) − 2; H(L) ≤ ψ(L)/(log T' − 4) + (64/(η log 2) + o(1))(log L)^2. Small zones cost O((log L)^{3/2}(log log L)^4) unconditionally (smaller pools P_y + VK at scale y).
- **VKGAP-C** [COND on NR(c,η)]: H(L) ≤ (64/(η log 2) + o(1))(log L)^2 ⇒ N(b) ≪ (log log b)^2, Erdős #18 Q1 (exponent 2) for m = Λ_L. Weaker NR'(exp(cL/(log L)^2), η) suffices.
- **RH** [COND on RH]: NR' up to T_RH = exp(c√L/log L) ⇒ H(L) ≪ √L log L, N(b) ≪ √(log b) log log b (Vose level up to log log).
- [PROVED] Sharpness: Dirichlet ⇒ NR_L(T,η) fails for T ≥ (8/η)^M (M ≥ 15).
- [REFUTED given PNT] NR from |τ| ≥ 1 fails for η > 1−|F(1)| = 0.019427… (|A(1)|/M → |F(1)| = 0.9805724; corrected by AUD3 from "0.0194"); all NR definitions start at |τ| ≥ 4 (sup|F| ≤ 3/√17 = 0.7276).
- sup_{|τ|≥1}|F| ≤ 0.9902 [PROVED]; exact 0.98057 and 1−|F| ≥ 0.0194τ^2 on (0,1] [NUMERICAL, certified].
- S3 regimes [PROVED]: constant gaps ⇒ L/log L; linear ⇒ (log L)^2; entropy-level ⇒ log L log log L.
- [HEUR] Method ceiling: L^1-Fourier / single-pool method stops at the linear regime ((log L)^2). Entropy-level conditional theorem [OPEN]. Fixed-size design recorded as [HEUR], not needed.
- [NUMERICAL] L = 10^4–10^6: Var(log p) ≈ 0.039 (proof uses 0.0059); max_{4≤τ≤2000}|A|/M = 0.716; min Σ(1−cos)/M ≈ 0.32 (proof needs 1/15); lattice dip 1−|A|/M ≈ 0.0196τ^2; maximal divisor gaps L ≤ 73.
- #304 and SP1 remain OPEN.

Files: code/vk_charfun.py, code/F_check.py, code/divgaps.py; out/vk_charfun.out, out/F_check.out, out/divgaps.out.

## Stage-2 audit (AUD3): 29 items — CONFIRMED 24, MINOR-FIX 5, GAP 0, WRONG 0
- VKGAP-A and VKGAP-B re-derived step by step, conditional on textbook inputs (E1)–(E4): cofactor ratio-≤2 lemma, smooth VK prime sum with Mellin contour shift, lattice band entering only via ∫e^{−c_2 nτ^2}; local-CLT constants recomputed exactly (lower bound 0.37604 ≥ 0.375, B ≤ 1.55429, tail 0.20322, margin 0.1717); coverage of [X_0, Λ/X_0] incl. top half; greedy bookkeeping; NR'⇒gaps; VKGAP-C; RH corollary; Dirichlet ceiling (8/η)^M; sup|F| ≤ 0.9902 — all confirmed.
- Fixes (`% AUD3:` in frag.tex): NR refutation threshold η > 1−|F(1)| = 0.019427…; limiting Var(log U) = 0.039094 (not 0.03907); Prop core tagged PROVED (+(E1)); entropy-level regime G(D) := G(L) for D > L (bound unchanged); RH corollary tag lists (E1),(E3),(E4); caveat that the lead's recalled RH truncated-formula error term is too strong at t=0 (no proof uses it).
