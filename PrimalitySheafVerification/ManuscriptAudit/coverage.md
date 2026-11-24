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
| 7. Geometric Reformulation of the Riemann Hypothesis | 227–298 | Spt7 |
| 8. Entropy–Growth and Sheaf Stability for Mock/Partial Theta and Jacobi Objects | 299–397 | Mock1, Mock1_Advanced |
| 9. Global Poincaré Matching and Kloosterman-Compatible Test Kernels | 398–458 | Mock2, Mock2_Advanced, Mock2_FunctionalAnalysis |
| 10. Modular q–Yang–Mills on Γ(2)∖ℍ | 459–507 | QYM, Mock3 |

[Numbered-label candidates](numbered-label-candidates.tsv) records 476 extraction hits. The index can include repeated labels or cross-references and miss irregularly typeset labels. Full claim-to-declaration mapping, including unnumbered claims, is in progress.

All 352,973 top-level Lean lines were read programmatically for inventory and search. See [source-reading progress](source-review.tsv) for the contiguous ranges read in detail. The ranges in this checkpoint cover 286,617 lines, including all lines of ten of the thirteen primary modules. Review of the remaining source is in progress. A Lean build checks declarations as stated. Assessing faithfulness requires comparing their definitions, quantifiers, and hypotheses with the manuscripts.

A [historical GitHub Actions run](https://github.com/leegahuyn/mathlib4/actions/runs/32707087421) passed the aggregate build and public BuildAll check. A Git tree comparison found 8,323 identical paths in scope, covering `Mathlib/**/*.lean`, top-level project Lean files, `Mathlib.lean`, `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` at both commits. The [fresh branch build and axiom audit](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/actions/runs/45300501006) combines compilation with a scan of elaborated declarations. The aggregate scanner evaluates Lean’s transitive axiom sets and reports project declarations outside the three-axiom allowlist. Axiom status is separate from manuscript fidelity.
