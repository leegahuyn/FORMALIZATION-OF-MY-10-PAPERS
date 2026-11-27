import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspClassicalAdicCohomology
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalClassicalAdicCohomology
import PrimalitySheafVerification.ManuscriptAudit.Paper7SameZetaDifferentCohomology

/-! Equal literal point-count zeta functions with different classical compact adic cohomology. -/

namespace ManuscriptAudit.Paper7SameZetaDifferentClassicalAdic

open CuspHasseWeilSeries Paper7SameZetaDifferentCohomology

noncomputable section

theorem same_zeta_distinct_classical_degree_one (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (hp₂ : p ≠ 2) (hℓp : ℓ ≠ p) :
    zetaOfCountSeries (NodalSchemeHasseWeil.properCounts p) =
      zetaOfCountSeries (nativeCuspCounts p) ∧
    ¬ Nonempty (IntegralNodalClassicalAdicCohomology.proper ℓ p 1 ≃+
      IntegralCuspClassicalAdicCohomology.affine p ℓ 1) := by
  refine ⟨equal_zeta p hp₂, ?_⟩
  have hp : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp₂)
  let node := IntegralNodalClassicalAdicCohomology.properAtOdd ℓ p hp hℓp 1 (by decide)
  letI : Subsingleton (IntegralCuspClassicalAdicCohomology.affine p ℓ 1) :=
    (IntegralCuspClassicalAdicCohomology.omitted p ℓ hℓp 1).1 (by decide)
  rintro ⟨e⟩
  let f := node.symm.trans e
  exact zero_ne_one (f.injective (Subsingleton.elim (f 0) (f 1)))

end
end ManuscriptAudit.Paper7SameZetaDifferentClassicalAdic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper7SameZetaDifferentClassicalAdic.same_zeta_distinct_classical_degree_one
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
