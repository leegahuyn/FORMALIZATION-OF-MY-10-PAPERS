import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.SlashActions
import PrimalitySheafVerification.ManuscriptAudit.FiniteIndexWeightZeroCosets

/-! The native weight-two right-coset trace of an invariant Green current. -/

namespace ManuscriptAudit.Paper8WeightTwoCosetTrace

open UpperHalfPlane ModularForm FiniteIndexWeightZeroCosets
open scoped MatrixGroups ModularForm

noncomputable section

def cosetSlash (H : Subgroup SL(2, ℤ)) (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → f ∣[(2 : ℤ)] h = f) :
    RightCoset H → ℍ → ℂ :=
  Quotient.lift (fun a : SL(2, ℤ) => f ∣[(2 : ℤ)] a) (fun a b hab => by
    have h : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp hab
    calc
      _ = (f ∣[(2 : ℤ)] (b * a⁻¹)) ∣[(2 : ℤ)] a := by rw [hf _ h]
      _ = f ∣[(2 : ℤ)] ((b * a⁻¹) * a) :=
        (SlashAction.slash_mul 2 (b * a⁻¹) a f).symm
      _ = _ := by simp [mul_assoc])

theorem cosetSlash_mk (H : Subgroup SL(2, ℤ)) (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → f ∣[(2 : ℤ)] h = f) (g : SL(2, ℤ)) :
    cosetSlash H f hf (rightCosetMk H g) = f ∣[(2 : ℤ)] g :=
  rfl

theorem cosetSlash_action (H : Subgroup SL(2, ℤ)) (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → f ∣[(2 : ℤ)] h = f)
    (q : RightCoset H) (g : SL(2, ℤ)) :
    cosetSlash H f hf q ∣[(2 : ℤ)] g = cosetSlash H f hf (rightCosetMul H g q) := by
  refine Quotient.inductionOn q (fun a => ?_)
  change (f ∣[(2 : ℤ)] a) ∣[(2 : ℤ)] g = f ∣[(2 : ℤ)] (a * g)
  exact (SlashAction.slash_mul 2 a g f).symm

def trace (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → f ∣[(2 : ℤ)] h = f) (z : ℍ) : ℂ :=
  letI := rightCosetFintype H
  ∑ q : RightCoset H, cosetSlash H f hf q z

theorem trace_slash (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → f ∣[(2 : ℤ)] h = f) (g : SL(2, ℤ)) :
    trace H f hf ∣[(2 : ℤ)] g = trace H f hf := by
  letI := rightCosetFintype H
  funext z
  rw [SL_slash_apply]
  unfold trace
  rw [Finset.sum_mul]
  refine Fintype.sum_equiv (rightCosetMul H g) _ _ (fun q => ?_)
  simpa only [SL_slash_apply] using congrFun (cosetSlash_action H f hf q g) z

theorem trace_vanishes (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (f : ℍ → ℂ)
    (hf : ∀ h : SL(2, ℤ), h ∈ H → f ∣[(2 : ℤ)] h = f) (z : ℍ)
    (hz : ∀ g : SL(2, ℤ), f (g • z) = 0) :
    trace H f hf z = 0 := by
  letI := rightCosetFintype H
  unfold trace
  apply Finset.sum_eq_zero
  intro q _
  refine Quotient.inductionOn q (fun a => ?_)
  change (f ∣[(2 : ℤ)] a) z = 0
  rw [SL_slash_apply, hz a, zero_mul]

end
end ManuscriptAudit.Paper8WeightTwoCosetTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8WeightTwoCosetTrace.cosetSlash_action,
      ``ManuscriptAudit.Paper8WeightTwoCosetTrace.trace_slash,
      ``ManuscriptAudit.Paper8WeightTwoCosetTrace.trace_vanishes] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
