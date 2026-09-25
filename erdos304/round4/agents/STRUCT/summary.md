# STRUCT summary (Round 4) — in progress

Files: `frag.tex` (Korean LaTeX fragment), `code/`, `out/`.

## S1 Dedup (done)
- STRUCT:lem-swap, STRUCT:thm-dedup [PROVED]: for any N with property (*) ("every odd prime p | N has (p+1)/2 | N"),
  repetition-allowed min = distinct min for 0 <= a < N; swap count <= min((a^2-Phi0)/2, (s-1)+(sum log d_i+(s-1)log2)/log(4/3)).
- STRUCT:thm-char [PROVED, new]: dedup property <=> (*). If (*) fails at p, a* = 2N/p has multiset-min 2 < distinct-min (>=3).
  Lambda_L, n!, 2^n satisfy (*); N=10 does not (a=4, a=9) [REFUTED general claim].
- NUMERIC (code/dedup_check.py, out/dedup_check.out): g=g~ for all a<Lambda_L, L<=16; (*)<=>dedup for all N<=6000 (283 vs 5716);
  witness a* verified for 9286 pairs; 3000 random swap runs OK.
- Corollaries [PROVED]: practicality of (*)-numbers; H(L)=min{k: k(D*∪{0}) ⊇ [0,Λ)}; Bellman; subadditivity;
  cascade assembly with overlapping families (SP1-disj, label designs, u-robustness unnecessary for Λ_L);
  ordered-tuple count r_K(n)>0 suffices (Newton/E4 in baker Ch.12 unnecessary). Remark: restricted-family versions are NOT preserved.
