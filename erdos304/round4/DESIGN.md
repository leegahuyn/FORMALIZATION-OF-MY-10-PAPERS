# DESIGN — Round 4 targets and the lead's structural observations

Read `BRIEF.md` first. Each observation S# is the lead's claim, marked **(verify)**: you must re-derive it before using it, and report if it is false.

## Where we are

Round 1–3 (corpus) reduced #304 to the single core **SP1 ⇔ H(L) ≪ log L** (OPEN). Round 4 does NOT expect to prove SP1. Its goals, in order:
1. Prove the strongest honest **new unconditional** theorems toward SP1 (targets VKGAP, CMM).
2. Build a rigorous **ladder of conditional theorems** that pins down exactly which arithmetic statement yields which bound (`L/log L → L/(log L)^{3/2} → L^{1−δ} → (log L)^2 → log L log log L → log L`), with the implications proved and the hypotheses stated sharply (STRUCT, VKGAP).
3. Extend exact numerics (NUM).

## S1. Dedup ⇒ multiset formulation (verify)

Baker Thm 3.2 (baker 461–499): for `0 ≤ a < Λ_L`, the least number of divisors with repetition = least number of distinct divisors. Proof: a repeated `d` has `2d ≤ a < Λ`; let `p` = least prime with `v_p(d) < a_p`. If `p = 2`: `d+d = 2d`. If `p ≥ 3`: `r = (p+1)/2 < p`, all prime powers of `r` are ≤ `r ≤ L` and involve primes `< p` where `d` has full exponent, so `r | d`; `d + d = pd/r + d/r`, both divide `Λ`, both `< 2d ≤ a`, and `Φ = Σ d_i^2` increases by `(u−v)^2/2 ≥ 2`; `Φ ≤ a^2` ⇒ termination.
Consequences: `H(L) = min{k : k·(D*_L ∪ {0}) ⊇ [0,Λ_L)}` (sumset with repetition). **No disjointness bookkeeping is ever needed**: cascade stages may reuse divisors; Newton/E4 corrections in baker Ch.12 are unnecessary (count ordered tuples with repetition); label-disjoint designs (p1p4 Prop 8.21) are unnecessary.

## S2. Block (bundled mixed radix) schemes (verify)

A block scheme is a chain `1 = N_0 | N_1 | … | N_t = Λ_L`, `b_j = N_j/N_{j−1}`, `W_j = Λ/N_j`; `a = Σ c_j W_j`, `0 ≤ c_j < b_j`; stage `j` needs: every `c < b_j` is a sum of ≤ `K_j` divisors of `N_j` (repetition allowed). Then `H(L) ≤ Σ K_j` [PROVED, easy with S1].
- Self-similar special case: `H(L) ≤ H(y) + T(L,y)`, `T(L,y)` = max over `c < Λ_L/Λ_y` of the least number of divisors of `Λ_L` summing to `c`.
- Counting per block: `(1 + #{e | N_j : e < b_j})^{K_j} ≥ b_j` (multisets).
- **Claim (verify, make rigorous with explicit constants):** for `N_j = Λ_{y_j}` with `log b_j ≍ w·y_j` for a fixed `w ∈ (0,1)` (geometric blocks), `Σ K_j ≥ c(w)(log L)^2`. A single block (`t=1`) is SP1 itself, so the barrier concerns multi-block schemes with bounded scale ratio; superexponential blocks (`y_j = L^{2^{−j}}`) are cost-`O(log L)` only if each block is essentially SP1 at its scale.
- **Conditional (verify):** `BC*(w,C)`: for all large `y`, every `c < Λ_y^{w}` is a sum of ≤ `C log y` divisors of `Λ_y` ⇒ `H(L) ≪_{w,C} (log L)^2` ⇒ `N(b) ≪ (log log b)^2` and Erdős #18 Q1 (strong form) for `m = Λ_L`. Note `BC*` is strictly weaker-looking than SP1 but still requires exponentially fine covering.

## S3. Greedy / gap ladder (verify)

p1p4 Prop 5.18: `GH(δ,X0)` ⇒ `H ≤ log_2 X0 + log Λ/log(1/δ) + O(log X0/log L)`. Generalise to a **scale-dependent** gap `δ(ℓ)` at `x = e^ℓ`: `ℓ_{i+1} ≤ ℓ_i − log(1/δ(ℓ_i))`. Record the three regimes:
- `log(1/δ(ℓ)) ≍ log L` (primes in short intervals) ⇒ `H ≪ L/log L` (no gain).
- `log(1/δ(ℓ)) ≥ c ℓ/log L` (linear-entropy gaps) ⇒ `H ≪ (log L)^2`.
- `log(1/δ(ℓ)) ≥ c (ℓ/log L) log(eL/ℓ)` (entropy-level gaps, `DG`) ⇒ `H ≪ log L log log L` (matches the greedy barrier, p1p4 Thm 5.16).
Greedy can never beat `log L log log L`; SP1 needs non-greedy multi-scale stages.

## S4. Nonresonance ⇒ divisor gaps (target VKGAP; verify every step)

Define `NR(P',T,η)`: `|Σ_{p∈P'} w_p p^{iτ}| ≤ (1−η) Σ w_p` for `1 ≤ |τ| ≤ T` (`P'` a set of primes with exponent 1 in `Λ`, weights `w_p`).

**Lead's sketch of the main new theorem.**
- Random divisor: independent `ξ_p ~ Bernoulli(q_p)`, `S = Σ ξ_p log p`, `U = ∏_{ξ_p=1} p`; `φ_S(τ) = ∏(1 − q_p + q_p p^{iτ})`, `|1−q+qe^{iα}|^2 = 1 − 2q(1−q)(1−cos α)` ⇒ `|φ_S(τ)| ≤ exp(−Σ q_p(1−q_p)(1−cos(τ log p)))`.
- Cofactor shift: divisors of `Q` (or of `Q' = ∏_{p ∉ P'} p^{a_p}`) have consecutive ratio ≤ 2 (check!), so `log c` can be placed within `log 2` of any value in `[0, log Q]`; target `ℓ = log x` is reached by `d = c·U` with `S` in the bulk `|S − µ| ≤ √V`, `µ = Σ q_p log p`, `V = Σ q_p(1−q_p)(log p)^2`.
- Frequency ranges for the plain pool `P = (L/2, L]`, `q_p = q`, `n = qM`:
  (i) `|τ| ≤ π/log L`: `1−cos(τ log p) ≥ (2/π^2)(τ log p)^2` ⇒ Gaussian decay `exp(−cVτ^2)`.
  (ii) `π/log L ≤ |τ| ≤ 1`: **WARNING — lattice resonance.** `log p = log L − u_p`, `u_p ∈ [0, log 2)`, so `S ≈ N log L − Σ ξ_p u_p` is near-lattice with span `log L`: `|φ_S(2π/log L)|` is only `≤ exp(−c n/(log L)^2)`. Use `1 − |Σ_P p^{iτ}|^2/M^2 = E(1 − cos τ(u−u'))` (pair argument, `|τ(u−u')| < π`) `≥ (4/π^2)τ^2 Var(u)`, `Var(u) ≥ c` by PNT. Hence need `n ≥ C (log L)^3` (i.e. `ℓ ≥ C (log L)^4`) in this design. Alternative designs (weights spread over `(√L, L]` so `log p` is spread over an interval of length `≍ log L`) remove the lattice problem; optional.
  (iii) `1 ≤ |τ| ≤ 10`: PNT: `Σ_{p∈P} p^{iτ} = (1+o(1)) M·F(τ)`, `|F(τ)| = |2 − 2^{−iτ}|/|1+iτ| = sqrt(5 − 4cos(τ log 2))/sqrt(1+τ^2) ≤ 0.99` for `|τ| ≥ 1` (check numerically).
  (iv) `10 ≤ |τ| ≤ T_VK := exp((log L)^{3/2}(log log L)^{−3})`: **Vinogradov–Korobov** zero-free region + explicit formula ⇒ `Σ_{n≤x} Λ(n) n^{−iτ} = x^{1−iτ}/(1−iτ) + O(x exp(−c log x/((log T)^{2/3}(log log T)^{1/3})))` for `|τ| ≤ T` (textbook `\EXT`, e.g. Titchmarsh §6.19 + explicit formula; state the version you use). The error is `o(M)` for `x = L`, `T ≤ T_VK`; main term `≤ 3M/|τ|`. So `NR(P, T_VK, 0.01)` holds unconditionally for large `L`.
- Local count via **Fejér kernel** `F_T(x) = T(sin πTx/(πTx))^2 ≥ 0`, `F̂_T = (1−|ξ|/T)_+`: `E F_T(S − s) = ∫_{|ξ|≤T}(1−|ξ|/T) e(−ξs) φ_S(2πξ) dξ`. Main term from (i) `≈ (2πV)^{−1/2} e^{−(s−µ)^2/2V}` (local CLT with cubic error `O(n^{−1/2})`); ranges (ii)–(iv) contribute `≤ 2T e^{−cn} + e^{−cn/(log L)^2}`, negligible if `n ≥ C max(log T, (log L)^3)`. Tail of `F_T` outside `[s−h, s+h]`: `≤ Σ_j P(S ∈ J_j)/(π^2 T j^2 h^2)` with an **upper** local bound `P(S ∈ J) ≤ C(|J| + 1/T)/√V` (Beurling–Selberg majorant with Fourier support `[−T,T]`) ⇒ tail `≪ 1/(Th√V)`. With `h = L/T`: `P(|S − s| ≤ h) > 0` for `|s − µ| ≤ √V`.
- Conclusion (target theorem **VKGAP-A**): for `L ≥ L_0(ε)`, every `x ∈ [X_0, Λ_L/X_0]`, `X_0 = exp(C(log L)^4)`, has a divisor of `Λ_L` in `[(1 − δ)x, x]`, `δ = exp(−(log L)^{3/2−ε})` (top half by symmetry `d ↦ Λ/d`).
- ⇒ **VKGAP-B (new unconditional):** `H(L) ≤ (1+o(1)) L/(log L)^{3/2−ε}` (S3 + small-residue theorem for `R < X_0`, which costs `O((log L)^3)`), hence `N(b) ≪ log b/(log log b)^{3/2−ε}`. (Weaker than Hughes' factorial bound for `N(b)`, but new for `Λ_L`; the divisor-gap theorem itself is the main content — compare Berend–Harmse for `n!`.)
- **VKGAP-C (conditional, multi-scale):** `NR(P, e^{cM}, η)` for a fixed `c, η > 0` ⇒ at scale `ℓ` use `n ≍ ℓ/log L`, resolution `T(ℓ) = min(e^{cM}, e^{ηn/C})` ⇒ `log(1/δ(ℓ)) ≫ ℓ/log L` ⇒ `H(L) ≪ (log L)^2` (small zone `ℓ ≤ (log L)^4` must also cost `O((log L)^2)`: use small pools `(y/2,y]` + VK there, or explain). Sharpness: by Dirichlet's simultaneous approximation, `NR(P,T,η)` **fails** for `T ≥ (C/η)^{M}` — so exponential height is the natural limit (verify).

## S5. Composite-modulus mixing (target CMM; verify)

Setting: p1p4 Def 4.4 (independent uniform exponents of `c_i | Q`, uniform `t_i`-subset `E_i ⊆ P_i`), `µ_i(θ) = E e(θ c_i U(E_i))`. Known (Thm 4.19): for prime `3 ≤ p ≤ L/2`, `µ_i(a/p) = π_p − (1−π_p)/(p−1) + O((1−π_p) ε_L(p))`.
Target: squarefree `q = q_1⋯q_ω | Q`, all `q_j ∈ (√L, L/2]` (so `π_{q_j} = 1/2`), `(a,q)=1`, `ω ≤ c L^{1/4}/log L`:
`µ_i(a/q) = ∏_j (1/2 − 1/(2(q_j−1))) + (error)` with error small **relative to `2^{−ω}`**, giving `|µ_i(a/q)| ≤ ∏_j (1/2 + ε_L)`, `ε_L = O(L^{−1/4}(log L)^2)` (or whatever the proof gives).
Lead's sketch: condition on `J = {j : q_j | c_i}` (independent events, prob 1/2 each). On `J`, `e(aX/q) = e(Σ_{j∉J} a_j X/q_j)` and `X ≡ m·c'·U` with `m` a unit mod `q' = ∏_{j∉J} q_j`, `c'` the part of `c_i` coprime to `q`. Expand `e(by/q')` over characters mod `q'` (Gauss sums factor by CRT: `|τ(χ)| = ∏_{j∈supp χ} √q_j`, trivial components give Ramanujan sums `−1`). Principal part gives `∏_{j∉J} (−1/(q_j−1))`. For `χ` with support `S ≠ ∅`: `|Eχ(c')| ≤ ∏_{p∈P'} |1+χ(p)|/2 ≤ exp(−(N_1 − Re A(χ))/4)`, `A(χ) = Σ_{p∈P'} χ(p)`, `P' = (√L, L/2] \ {q_j}`. Bad characters (`|A| ≥ N_1/2`) counted by the **2k-th moment**: `Σ_{χ mod q_S} |A(χ)|^{2k} = φ(q_S)·#{∏p_i ≡ ∏p'_i (mod q_S)} ≤ φ(q_S) N_1^k k! ((L/2)^k/q_S + 1)`; choose `k = ⌈log q_S/log(L/2)⌉`. Resulting error for support `S`: `≲ (C k log L)^k/√q_S + √q_S e^{−N_1/8}`. Then sum over `S` and `J` with weights.
Deliverables: the theorem with explicit constants/ranges; consequence: the extended singular series over such `q` converges for `s ≥ (2+δ) log_2 L` windows (upgrade of p1p4 Cor 4.20 / Remark 4.21 / (T3) from HEURISTIC to PROVED in this range); discuss what remains (small prime factors `≤ √L`, prime powers, `ω > cL^{1/4}/log L`), numerically check the formula for small `L` (`h'=2,3`).

## S6. Smooth-number route (part of STRUCT; verify)

Baker Ch.12–13: literature inputs (Drappeau–Shao arXiv:1602.07885 Thm 2.4 & Lemma 3.2; Harper arXiv:1408.1662 weighted restriction Thm 2, `p=3`) ⇒ every `n ∈ [L, e^{L^δ}]` is a sum of 4 proper divisors ⇒ blocks with `log b_j ≤ y_j^δ` ⇒ `H(L) ≪ L^{1−δ}`. With S1 the distinctness/Newton step disappears. General form: if "every `n ≤ x` is a sum of `K` numbers that are `y`-smooth with `y ≥ (log x)^C`" holds quantitatively, then `H(L) ≪ L^{1−1/C}`; beating Vose (`N(b) ≪ (log b)^{1/2−c}`) needs `C < 2`; entropy allows `C > K/(K−1)`. Record what the literature gives (search snippets: Harper; Lagarias–Soundararajan `a+b=c` in `(log x)^κ`-smooth numbers, `κ > 8` under GRH — recalled, verify by search).

## S7. Numerics (target NUM)

- With S1, `H(L)` = number of BFS levels of the sumset iteration `R_k = R_{k−1} + (D* ∪ {0})` on a bitset of length `Λ_L`. Compute **`H(23) = H(24)`** (`Λ_23 = 5 354 228 880`, `τ = 1920`, bitset 669 MB); cross-check against the old 0/1-DP values for `L ≤ 19`; record the κ-histogram, `a_c = min{a : κ(a)=c}`, and whether the max is attained only in `[Λ/2, Λ)`. Optional in background: `L = 25` (3.35 GB bitset) only if the first finished early.
- Nonresonance experiment for S4/VKGAP-C: for pools `P = (L/2, L]` with `M ≤ ~30`, estimate the first resonance height `τ*(L,η) = min{τ ≥ 1 : |Σ p^{iτ}| ≥ (1−η)M}` (grid + refinement, or LLL-style simultaneous approximation) and test `log τ* ≍ M`.
- Check `max_{|τ|≥1} |F(τ)|` of S4(iii) and `Var(u)` of S4(ii) numerically.

## S8. Agent roster (Stage 1)

| ID | Target | Deliverable |
|---|---|---|
| VKGAP | S4 (A, B, C) + S3 regimes | new unconditional divisor-gap theorem and `H(L) ≪ L/(log L)^{3/2−ε}`; conditional `NR(e^{cM}) ⇒ (log L)^2` |
| CMM | S5 | composite-modulus mixing theorem, singular-series consequence, numerics |
| STRUCT | S1, S2, S3 (implications), S6, ladder table | rigorous structural theorems, barrier for geometric blocks, conditional ladder, smooth route restated with dedup |
| NUM | S7 | `H(23)`, histograms, resonance-height data |
| CORE | SP1 directly | three honest attempts at SP1 or a strict intermediate step; rigorous method-barrier theorems |

Stage 2: two auditors (different agents) re-derive everything tagged PROVED/REFUTED.
