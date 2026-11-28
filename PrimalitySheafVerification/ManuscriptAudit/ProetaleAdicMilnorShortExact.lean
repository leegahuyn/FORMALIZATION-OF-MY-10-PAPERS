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

section Quotient

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
  (d : G →+ G) (c : G →+ H) (h : c.ker = d.range)

private def quotientInclusion : (G ⧸ d.range) →+ H :=
  QuotientAddGroup.lift _ c h.symm.le

private theorem quotientInclusion_injective :
    Function.Injective (quotientInclusion d c h) :=
  (QuotientAddGroup.injective_lift_iff _ c _).2 h.symm

private theorem quotientInclusion_range : (quotientInclusion d c h).range = c.range := by
  ext a
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective d.range v
    exact ⟨u, hv⟩
  · rintro ⟨u, hu⟩
    exact ⟨QuotientAddGroup.mk' d.range u, hu⟩

private theorem quotientInclusion_exact {J : Type*} [AddCommGroup J]
    (ρ : H →+ J) (hr : c.range = ρ.ker) (x : H) :
    (∃ y, quotientInclusion d c h y = x) ↔ ρ x = 0 := by
  have h' := (quotientInclusion_range d c h).trans hr
  exact Iff.of_eq (congrArg (fun A : AddSubgroup H ↦ x ∈ A) h')

end Quotient

set_option maxHeartbeats 1000000

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ)

abbrev firstDerivedLimit := Tuples X ℓ d ⧸ (differenceTuples X ℓ d).range

/-- The genuine connecting map on the actual quotient of product coordinates. -/
abbrev inclusion :=
  quotientInclusion (differenceTuples X ℓ d) (connecting X ℓ d) (connecting_kernel X ℓ d)

/-- The native reduction forms a short exact sequence with the quotient of the
preceding positive-degree product by the consecutive difference. -/
theorem exact_sequence :
    Function.Injective (inclusion X ℓ d) ∧
    (∀ x, (∃ y, inclusion X ℓ d y = x) ↔ reductionMap X ℓ (d+2) x = 0) ∧
    Function.Surjective (reductionMap X ℓ (d+2)) := by
  let D := differenceTuples X ℓ d
  let c := connecting X ℓ d
  let h := connecting_kernel X ℓ d
  exact ⟨quotientInclusion_injective D c h,
    quotientInclusion_exact D c h (reductionMap X ℓ (d+2)) (connecting_range X ℓ d),
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
