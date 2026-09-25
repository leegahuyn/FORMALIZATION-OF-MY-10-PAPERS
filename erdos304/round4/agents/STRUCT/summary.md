# STRUCT summary (Round 4) — final
(Lead may overwrite. Full ledger is also inside frag.tex, subsection "상태 원장 (STRUCT)".)

Files: `frag.tex` (13 pp., COMPILE OK), `code/dedup_check.py` -> `out/dedup_check.out`, `code/block_opt.py` -> `out/block_opt.out`.

## S1 Dedup
- STRUCT:thm-dedup [PROVED]: if N has (*) (every odd prime p|N has (p+1)/2 | N), multiset-min = distinct-min for 0<=a<N;
  swaps <= min((a^2-Phi0)/2, (s-1)+(sum log d_i+(s-1)log2)/log(4/3)).
- STRUCT:thm-char [PROVED, new]: dedup property <=> (*); if (*) fails at p then a*=2N/p has multiset-min 2 < distinct-min.
  Lambda_L, n!, 2^n have (*). N=10, a=4 (and 9) [REFUTED general claim].
- NUMERIC: equality for all a<Lambda_L (L<=16); (*)<=>dedup for all N<=6000; 3000 random swap runs OK.
- Corollaries [PROVED]: H(L)=min{k: k(D*∪{0}) ⊇ [0,Λ)}; Bellman; subadditivity; cascades with overlapping families
  (SP1-disj, label designs, u-robustness unnecessary for Λ_L); ordered K-tuple count >0 suffices (Newton/E4 unnecessary).

## S2 Block schemes
- H(L) <= sum K_j; H(L) <= H(y)+T(L,y) [PROVED]. Divisor-count lemma (p1p4 8.34 re-verified, generalised).
- Barrier [PROVED, PNT]: Λ-type schemes with ν_j=log b_j/ψ(y_j) <= w: sum K_j >= H(y_1)+c(w)[(1-ε)(log L)^2-(log y_1)^2],
  c(w)=1/(2(1+log(1/w))log(1/(1-w))); c(1/4)=.7283, c(1/2)=.4260, c(3/4)=.2801, c(.9)=.1964.
- Escape only via SP1-at-scale [PROVED]: SP1 <=> T(y,y^λ) << log y <=> superexponential chains cost O(log L).
- BC*(w,C) => limsup H/(log L)^2 <= C/(2log(1/(1-w))) => N(b) << (log log b)^2, Erdős #18 Q1 with exponent 2 for m=Λ_L [COND].
  Best C from counting gives exactly c(w): barrier constant is sharp within geometric schemes.
- NUMERIC: DP lower bound for optimal Λ-type schemes (y_1<=22), L=5000: 58/38/30/24 (w=1/4,1/2,3/4,.9).

## S3 Greedy ladder
- Scale-dependent greedy lemma [PROVED]: H <= H(y0)+1+∫ dℓ/λ_*(ℓ)+ceil(log X0/log(L/2)); small zone: R<(L/2)^k uses <=k terms if k<=M.
- Regimes [PROVED implications]: (A) log(1/δ)>=c log L => (1/c+o(1))L/log L; (B) >= cℓ/log L => (1/c+o(1))(log L)^2;
  (C) DG(c) => (1/c+o(1)) log L log log L.
- DG(c) is FALSE for c>1 [REFUTED, via Rankin]. Under DG: greedy Θ(log L log log L) (lower bound = p1p4 Thm 5.16).

## S6 Smooth route
- W_Λ(K,C) => limsup H/L^{1-1/C} <= KC/(C-1) [COND]; baker Ch.13 count re-verified (dyadic const 2/(1-2^{δ-1})).
- Entropy: W needs C >= K/(K-1) [PROVED]. Deletion needs α>1/2, fails for α<1/2 [PROVED]; α→1-1/C (recalled) => deletion needs C>2.
- (E1)-(E4) & C>2 => W_Λ(K,C) [COND]. Beating Vose needs C<2: impossible via smooth numbers + deletion.
- Literature: Harper (p>2 moments, log^{C(p)}x<=y; a+b=c count for log^C x<=y) snippet-verified; Drappeau–Shao abstract snippet-verified,
  baker's Thm 2.4/Lemma 3.2 recalled; L–S GRH κ>8 snippet-verified. Literature gives only L^{1-δ}, small δ (weaker than Vose).

## Stage-2 audit (AUD2): 42 items — CONFIRMED 32, MINOR-FIX 9, GAP 1, WRONG 0
- GAP (tag downgraded): rem-smooth-honest (2) "smooth numbers + deletion can in principle never beat Vose" was tagged PROVED; only the narrower statement is proved (the specific deletion upper bound is useless for α ≤ 1/2). The "in principle" claim needs a lower bound nobody proved → split into PROVED / EXT / HEUR; ladder row qualified. **This summary's earlier wording on the deletion claim is superseded.**
- Main minor fix: (E3) (de la Bretèche–Tenenbaum ratio bound) narrowed to k ≤ n/y as in the snippet; proof patched (n ≥ y^3 direct; y < n < y^3 via STRUCT's small-residue lemma with 4 primes in (y/2, y], y ≥ 29, Ramanujan; checked to 2·10^6).
- Other minor fixes: prop-escape (c)(3) y_0 quantified, (d) missing direction added; thm-barrier justification line; thm-BC sum bound for large L; rem-S3-meaning (1) scope limited to ℓ ≈ L/4; prop-entropy-W σ > 0; rem-smooth-honest (4) count added (threshold K/(K−1) exact for divisors of Λ_y); Vose citation page fixed. Hildebrand's saddle-point formula upgraded to snippet-verified (α → 1 − 1/C).
- All 15 edits marked `% AUD2:` in frag.tex; backup frag.tex.orig_before_AUD2.
