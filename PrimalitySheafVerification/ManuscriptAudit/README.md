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

The inventory is a byte-level baseline. Semantic review of the manuscripts and Lean modules, source-to-declaration mapping, and fresh kernel verification are in progress. The historical build record in the source tree points to a different repository and commit and cannot serve as a fresh check of this snapshot.
