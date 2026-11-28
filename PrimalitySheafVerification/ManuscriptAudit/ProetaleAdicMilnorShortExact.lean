import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Defs
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicMilnorConnecting

/-! The native Milnor short exact sequence, using the literal cokernel
presentation of the first derived limit of a countable tower. -/

namespace ManuscriptAudit.ProetaleAdicMilnorShortExact

open AlgebraicGeometry CategoryTheory
open ProetaleAdicMilnorConnecting
open ProetaleAdicReductionAllDegrees

noncomputable section

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ)

abbrev firstDerivedLimit := Tuples X ℓ d ⧸ (differenceTuples X ℓ d).range

/-- The genuine connecting map descends to the actual countable cokernel. -/
def inclusion : firstDerivedLimit X ℓ d →+ X.EllAdicCohomology ℓ (d+2) :=
  QuotientAddGroup.lift _ (connecting X ℓ d) ((connecting_kernel X ℓ d).symm.le)

theorem inclusion_injective : Function.Injective (inclusion X ℓ d) :=
  (QuotientAddGroup.injective_lift_iff _ (connecting X ℓ d) _).2 (connecting_kernel X ℓ d).symm

theorem inclusion_range :
    (inclusion X ℓ d).range = (reductionMap X ℓ (d+2)).ker := by
  rw [← connecting_range X ℓ d]
  ext a
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective (differenceTuples X ℓ d).range v
    exact ⟨u, hv⟩
  · rintro ⟨u, hu⟩
    exact ⟨QuotientAddGroup.mk' (differenceTuples X ℓ d).range u, hu⟩

/-- The native reduction sits in an actual short exact sequence with the countable
cokernel of the preceding positive-degree tower. -/
theorem exact_sequence :
    Function.Injective (inclusion X ℓ d) ∧
    (inclusion X ℓ d).range = (reductionMap X ℓ (d+2)).ker ∧
    Function.Surjective (reductionMap X ℓ (d+2)) :=
  ⟨inclusion_injective X ℓ d, inclusion_range X ℓ d,
    ProetaleAdicMilnorPositive.reduction_surjective X ℓ (d+1)⟩

end
end ManuscriptAudit.ProetaleAdicMilnorShortExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicMilnorShortExact.exact_sequence] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
