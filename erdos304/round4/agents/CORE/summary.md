# CORE — summary (written by the lead from the agent's final report)

Fragment: `frag.tex` (12 pp., compile OK; ledger §"상태 원장"). Pending audit (AUD4).

**Verdict:** SP1 [OPEN]. Strict intermediate steps also [OPEN]: H ≪ L^{1/2−c}; almost-all (or positive-proportion) O(log L) covering; one top stage with O(log L) terms.

## Barrier theorems
- **I. Mean-value/moment [PROVED]:** Σ|a_n|^2/δ_n ≥ (Σ|a_n|)^2/(2ℓ) ⇒ the moment + Montgomery–Vaughan bound for meas{|P| ≥ (1−2η)M} is ≥ (2e C_0/log 2)·η at every k and height, above the certification threshold 2η/log L; so pointwise NR is certified at no height. More generally any τ-translation-uniform bound (depending only on |a_n|, λ_n) is ≥ 2η/log L. Dirichlet: NR fails for T ≥ 2π⌈π√(2/η)⌉^M [PROVED]. **Correction to the lead's sketch:** "MV needs T ≥ e^{c'L}" is wrong; the obstruction is Σ a_n^2/δ_n, not the minimal spacing, and it kills pointwise certification at all heights.
- **II. Resolution [PROVED]:** any argument using only gap/cell-count information at relative resolution ρ = e^{−λ} plus exact data below X_0 cannot beat (1−o(1)) L/(λ + log L) (same-count sets: geometric progression / clustered divisors). ⇒ p1p4 Prop 5.18 optimal up to 1+o(1); VKGAP-B optimal for its input (even with local counts at VK resolution); SP1 (even one top stage) needs arithmetic information at resolution e^{−Θ(L/log L)}. At L=12 not yet biting [NUMERIC].
- **III. Fourier certificate [PROVED]:** required pointwise minor-arc saving averages (Jensen) exactly to the counting condition — the difficulty is uniformity over minor arcs; forces s ≥ (2/log 2) log L and every a/p major.
- **IV. Erdős #18 [PROVED]:** SP1 ⇒ strong #18 Q1 with exponent 1 (optimal); necessary and sufficient condition for #304 via the practical-number transfer. Correction: "log log M_{k+1} − log log M_k = O(1)" is sufficient, not necessary; right condition log log M_{k+1} = O(log log M_k). ⇒ SP1 along any sequence with L_{k+1} ≤ L_k^A implies #304.

## Direct attempts
- (b) Adaptive M [PROVED]: N(a,b) = lim_{L'} g_{Λ_{L'}}(aΛ_{L'}/b) (non-increasing), so N(Λ_L) ≤ H(L); no averaging available. N(60) = 4 = H(5) [PROVED]. For 2 ≤ L ≤ L' ≤ 19 the worst value never drops below H(L) [NUMERIC] (only the number of worst targets shrinks).
- (c) Second moment: coarse-coverage lemma |supp Y + [0,R_*)| ≥ 2/(π^2 ∫_{|θ|≤1/(2R_*)}|φ|^2) [PROVED]; **new unconditional count** #{a < Λ : g(a) ≤ C log L} ≥ exp((1/2 − o(1)) L log log L/log L) via p-adic injectivity [PROVED] (corpus: exp(O((log L)^2))). Gap to Λ^{1−o(1)} exponential; closing it needs cofactor mixing mod composites with ω ≍ L/(log L)^2 (beyond CMM). Pairwise additive energy of divisor sums ≈ (0.4–0.5) L N^2 non-trivial solutions [NUMERIC].
- (a) Modular stages: stage lemma and character criterion [PROVED]; needs all-character CMM at ω(q) ≳ L/(log L)^2; carries do not change counting; geometric chains cost ≥ c(θ)(log L)^2 [PROVED, COND only on Wigert's divisor bound].

## What new mathematics is needed
Equidistribution of sums of O(log L) products of primes from (L/2, L] at relative scale e^{−Θ(L/log L)}, from input that is neither τ-translation-invariant nor count-only. Cheapest next targets: SP1 along a sparse sequence; a non-trivial bound on P(|Y−Y'| < R_*); non-greedy stages beating VKGAP-C's (log L)^2.

Files: code/rescale_bfs.c → out/rescale_small.txt, out/rescale_16_17.txt, out/rescale_19.txt; code/energy2.c → out/energy2.txt; code/cluster_kappa.py → out/cluster_kappa_12.txt.
