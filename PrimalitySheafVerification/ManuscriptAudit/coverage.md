# Manuscript coverage

Three reading passes covered the readable text of physical PDF pages 1–507. Extracted formula layout can be ambiguous. Claim-specific review checks the original display where needed.

| Manuscript | PDF pages | Main Lean modules |
| --- | ---: | --- |
| 1. Primality Sheaf via Local Filters and Derived Equalizers | 5–26 | Verification, Spt1, Spt3 |
| 2. Master Equivalence on Arithmetic Curves | 27–51 | Spt2 |
| 3. A Primality Sheaf and Global Certification | 52–91 | Spt1, Spt3 |
| 4. Primality Sheaves and the Étale–Motivic–Derived Package | 92–145 | Spt4 |
| 5. Principal-Open Methods on Arithmetic Curves | 146–183 | Spt5 |
| 6. Equalizer–Tor, Gate Synchronization, and Étale–Motivic Detectors | 184–226 | Spt6 |
| 7. Geometric Reformulation of the Riemann Hypothesis | 227–297 | Spt7 |
| 8. Entropy–Growth and Sheaf Stability for Mock/Partial Theta and Jacobi Objects | 299–397 | Mock1, Mock1_Advanced |
| 9. Global Poincaré Matching and Kloosterman-Compatible Test Kernels | 398–458 | Mock2, Mock2_Advanced, Mock2_FunctionalAnalysis |
| 10. Modular q–Yang–Mills on Γ(2)∖ℍ | 459–507 | QYM, Mock3 |

[Numbered-label candidates](numbered-label-candidates.tsv) records 476 extraction hits. The index can include repeated labels or cross-references and miss irregularly typeset labels. The [crosswalk](numbered-label-crosswalk.tsv) links all 476 candidates to at least one inventory entry on the same physical PDF page. In 376 cases the normalized label occurs in the entry heading. In five more it occurs in the entry body. The other 95 links use the physical page. The page-based inventories for [Papers 1–3](inventory/papers-01-03.md), [Papers 4–7](inventory/papers-04-07.md), and [Papers 8–10](inventory/papers-08-10.md) record 317 groups, including substantive unnumbered claims. Pages 1–4 and 298 are preliminary material. The [claim comparisons](claim-comparisons.md) address 92 rows in detail and the [proof ledger](verified-declarations.tsv) identifies the exact audited revisions. Clause-level coverage across the full corpus is in progress.

The [source-reading record](source-review.tsv) covers all 352,973 top-level Lean lines at the pinned commit, including all thirteen primary modules. Review compared the substantive declarations and proof routes and inspected repetitive projections and audit commands as source. An additional lexical scan outside comments and ordinary strings found one `native_decide` call in the focused verification file at line 163. The same finite kernel cardinality has a [standalone proof by kernel reduction](LiteralRefutations.lean#L501). The scan found no `sorry`, `admit`, or explicit `axiom` tokens in the 17 baseline files. The transitive Lean audit remains the authoritative check. Claim-level comparison is in progress. A Lean build checks declarations as stated. Assessing faithfulness requires comparing their definitions, quantifiers, and hypotheses with the manuscripts.

A [historical GitHub Actions run](https://github.com/leegahuyn/mathlib4/actions/runs/32707087421) passed the aggregate build and public BuildAll check. A Git tree comparison found 8,323 identical paths in scope, covering `Mathlib/**/*.lean`, top-level project Lean files, `Mathlib.lean`, `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` at both commits. The [fresh branch build and axiom audit](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/actions/runs/45300501006) combines compilation with a scan of elaborated declarations. The aggregate scanner evaluates Lean’s transitive axiom sets and reports project declarations outside the three-axiom allowlist. Axiom status is separate from manuscript fidelity.


[LiteralRefutations.lean](LiteralRefutations.lean) contains the first new manuscript statements and counterexamples. The first check reached the runner without compiled vendored imports. The updated workflow builds the required vendored modules and runs an upstream compatibility check in parallel. The first vendored dependency build compiled 2,276 jobs and saved the cache key `manuscript-lean-imports-0e026509-linux-arm64-v1` in GitHub Actions. See the separate [claim-proof workflow](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/actions/workflows/manuscript-proofs.yml).
