# NUM — summary (written by the lead from the agent's final report)

Fragment: `frag.tex` (8 pp., compile OK; generated from `frag_src.tex` by `code/make_tables.py`, `res_analyze.py`, `assemble_frag.py`). Pending audit.

## Headline [NUMERICAL]
- **H(23) = H(24) = 7** (Λ = 5 354 228 880, τ = 1920). #{κ=7} = 167 987 582, all in [Λ/2, Λ). a_c (c=1..7): 1, 25, 5671, 2 486 867, 110 265 329, 1 039 438 397, 3 716 552 837. a_7 = Λ/2+Λ/6+Λ/38+Λ/874+Λ/134596+Λ/20996976+Λ/2677114440 (distinct).
- **H(25) = H(26) = 8** (Λ = 26 771 144 400, τ = 2880). Only 1158 values with κ=8, all within 0.73% of Λ. a_8 = 26 577 893 791 = Λ/2+Λ/3+Λ/7+Λ/63+Λ/1400+Λ/278460+Λ/66927861+Λ/5354228880. H first reaches 8 at L=25 (a prime power). Two independent BFS codes agree on all level and dyadic tables (609 s / 659 s; L=23: 108 s).
- For all L ≤ 26: H = 1 + max_{a<Λ/2} κ(a); moreover κ(Λ/2+b) = 1+κ(b) pointwise for all b (from counts via a proved counting lemma). General L: OPEN.

## Validation
- L = 2..22: p1p4 Tables 5–7 reproduced, 0 mismatches.
- Independent 0/1 DP (`dp01.c`): full κ array byte-identical to BFS for all 12 distinct Λ with L ≤ 19 (= all L ≤ 22) → numerical confirmation of the dedup theorem for L ≤ 22.
- BFS-independent checks: direct 3-divisor sum enumeration equals R_3 (L=23) and |R_3| (L=25); meet-in-the-middle confirms κ(a_7) ≥ 7 for L=23; 61 sample points agree. κ(a_8) ≥ 8 for L=25 relies on agreement of the two BFS codes only.

## Nonresonance (DESIGN S4)
- [PROVED, PNT as EXT] |Σ_P p^{i}|/M → |F(1)| = 0.98057 ⇒ NR(P,T,η) from |τ|=1 is false for η > 1−|F(1)| = 0.019427… (AUD3 correction of "0.0194"); need η < 0.0194 or cut-off τ_0(η) = 2.30, 3.31, 4.13 (η = 0.3, 0.2, 0.1).
- With cut-off 10: grid lower bounds with proved Lipschitz certificate (K ≤ (ln2/2) M), LLL resonances as upper bounds; M = 5..33. Fitted slopes of log10 τ* per prime: 0.21/0.30/0.50 (η = 0.3/0.2/0.1) vs random-phase model 0.25/0.35/0.52 [HEUR]. η = 0.1, M ≥ 21 bracketed only (M=33: 10^8.99 < τ* ≤ 10^18.68).

## Small checks
- sup_{|t|≥1} |F(t)| = |F(1)| = 0.980572 < 0.99 (certified bound). Var(u) → 0.039094 (limit proved from PNT; finite-L table).

Files: code/ (hbfs.c, hbfs2.c, dp01.c, resscan.c, lll_res.py, mitm*.c, build.sh); out/ (hbfs_L23.log, hbfs2_L25.log, hbfs_L25.log, bt_repr_L23.txt, repr_L25.txt, mitm23.txt, mitm25.txt, res_fit.txt); data/ (bfs/*.csv, resonance.csv, lll_res.csv, L25_kappa8.csv, var_u.csv). Level bitsets deleted (recomputable in 2–11 min).

## Stage-2 audit (AUD3): 15 items — CONFIRMED 14, MINOR-FIX 1, GAP 0, WRONG 0
- Dedup theorem, BFS validity and the counting lemma Z^+_k = Z^-_{k−1} ⇒ κ(Λ/2+b) = 1+κ(b) re-derived.
- **New (AUD3):** κ(a_8) ≥ 8 for L=25 (hence H(25) ≥ 8) verified without BFS: any ≤7-divisor sum equal to a_8 has largest term Λ/m, 2 ≤ m ≤ 7, and all six a_8 − Λ/m lie outside S_3+S_3. Upper bounds H(23) ≤ 7, H(25) ≤ 8 rest on BFS alone.
- MINOR-FIX: reproducibility caveat — lll_res.csv stores t to 15 digits, so LLL points with t ≳ 10^14 cannot be recomputed from the CSV.
- Independent checks: DP vs BFS agree at every a for L ≤ 18; L=23: |S_3| = |R_3| = 80 181 647, κ(a_7) ≥ 7, a_c bounds c=4–6; representations of a_7, a_8 verified; 21 grid resonance heights reproduced; K/M = 0.17–0.21; |F(1)| = 0.9805724.
- NOTE: AUD3 edited frag.tex directly; frag_src.tex is untouched — do NOT regenerate frag.tex from frag_src.tex without porting the `% AUD3:` edits.
