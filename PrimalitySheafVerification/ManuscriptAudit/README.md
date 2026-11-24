# Overleaf bundle formalization audit

| Input | Pinned reference |
| --- | --- |
| Attached PDF | 507 physical pages. SHA-256 `12eb737301b3312dbad255f7b6d2f74c43c9ba27a2955157c134d36c9c0e53c5`. |
| Lean sources | [master snapshot](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/tree/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification). |
| Lean toolchain | `leanprover/lean4:v4.33.0-rc1`. |

[Source inventory](baseline.tsv) records the complete byte and physical-line counts of the 17 top-level Lean files and the corresponding Git blob IDs. The 13 primary modules contain 352,735 lines. Including two integration bridges, the aggregate import file, and the focused verification file gives 352,973 lines. The experimental files under `FA_Blocker_WrapperCandidates` sit outside this inventory.

## Verification criteria

- Cite claims by physical PDF page, manuscript, and printed label where available. Include claims made outside numbered environments when they carry mathematical content.
- Match the source statement's objects, quantifiers, and hypotheses to the Lean declaration. Record a change of statement explicitly.
- Mark a claim verified or refuted only when the corresponding Lean proof passes on the pinned toolchain and its transitive axioms are audited. Standard Lean axioms are `propext`, `Classical.choice`, and `Quot.sound`. A hypothesis in the manuscript remains part of the statement. Assuming the conclusion or an unproved stronger replacement leaves the claim unresolved.
- Distinguish a counterexample to a statement from a flaw in its printed proof. Keep unresolved claims visible.

See [coverage](coverage.md), the [numbered-label candidates](numbered-label-candidates.tsv), and [selected claim findings](claims-first-pass.md). Full semantic source review, claim mapping, and declaration-level trust checks are in progress.

[Claim comparisons by manuscript](claim-comparisons.md) records 61 statement comparisons. The [new Lean declarations](LiteralRefutations.lean) and their [GitHub Actions workflow](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/actions/workflows/manuscript-proofs.yml) are separate from the pinned baseline build. Proof verification status is tracked by the workflow jobs for vendored and upstream Mathlib.
