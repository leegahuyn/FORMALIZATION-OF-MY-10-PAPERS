import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.InvolutionTensorComparison

/-!
# Base change of the two-copy tensor comparison

The fixed elements after any scalar extension are still the scalars.
Averaging by the invariant half proves this through tensor induction.
-/

namespace ManuscriptAudit.InvolutionTensorBaseChange

open scoped TensorProduct

noncomputable section

variable (A E B : Type*) [CommRing A] [CommRing E] [CommRing B] [Algebra A E] [Algebra A B]

private abbrev D := B ⊗[A] E
private abbrev right : E →ₐ[A] D A E B := Algebra.TensorProduct.includeRight

def baseSwap (σ : E ≃ₐ[A] E) : D A E B ≃ₐ[B] D A E B :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) σ

theorem baseSwap_tmul (σ : E ≃ₐ[A] E) (b : B) (x : E) :
    baseSwap A E B σ (b ⊗ₜ[A] x) = b ⊗ₜ[A] σ x := by
  rw [baseSwap, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul] <;> rfl

private theorem baseSwap_right (σ : E ≃ₐ[A] E) (x : E) :
    baseSwap A E B σ (right A E B x) = right A E B (σ x) :=
  baseSwap_tmul A E B σ 1 x

theorem baseSwap_involutive (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ) :
    Function.Involutive (baseSwap A E B σ) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => rw [baseSwap_tmul, baseSwap_tmul, hσ x]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem baseSwap_fixed_lifts (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ)
    (hFixed : ∀ x : E, σ x = x → ∃ a : A, algebraMap A E a = x)
    (h : E) (hHalfFixed : σ h = h) (hHalf : h + h = 1)
    (z : D A E B) (hz : baseSwap A E B σ z = z) :
    ∃ b : B, algebraMap B (D A E B) b = z := by
  let ih := right A E B h
  have hAverage (w : D A E B) :
      ∃ b : B, algebraMap B (D A E B) b = ih * (w + baseSwap A E B σ w) := by
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul b x =>
      have hx : σ (h * (x + σ x)) = h * (x + σ x) := by
        rw [map_mul, hHalfFixed, map_add, hσ x, add_comm (σ x) x]
      obtain ⟨a, ha⟩ := hFixed _ hx
      refine ⟨a • b, ?_⟩
      calc
        _ = b ⊗ₜ[A] (a • (1 : E)) := TensorProduct.smul_tmul a b 1
        _ = b ⊗ₜ[A] (h * (x + σ x)) := by
          rw [← Algebra.algebraMap_eq_smul_one, ha]
        _ = _ := by
          change _ = ((1 : B) ⊗ₜ[A] h) * ((b ⊗ₜ[A] x) + baseSwap A E B σ (b ⊗ₜ[A] x))
          rw [baseSwap_tmul, ← TensorProduct.tmul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      refine ⟨a' + b', ?_⟩
      rw [map_add, ha', hb', map_add]
      ring
  have hHalf' : ih + ih = 1 := by
    change right A E B h + right A E B h = 1
    rw [← map_add, hHalf, map_one]
  obtain ⟨b, hb⟩ := hAverage z
  refine ⟨b, hb.trans ?_⟩
  rw [hz, mul_add, ← add_mul, hHalf', one_mul]

/-- The canonical tensor comparison for the involution survives arbitrary scalar extension. -/
theorem baseChange_comparison_bijective (σ : E ≃ₐ[A] E)
    (hσ : Function.Involutive σ)
    (hFixed : ∀ x : E, σ x = x → ∃ a : A, algebraMap A E a = x)
    (h coefficient u v : E) (hHalfFixed : σ h = h) (hHalf : h + h = 1)
    (hc : σ coefficient = coefficient) (hu : σ u = -u) (hv : σ v = -v)
    (hPartition : coefficient * u ^ 2 + v ^ 2 = 1) :
    Function.Bijective (InvolutionTensorComparison.comparison (B) (D A E B) (baseSwap A E B σ)) := by
  let i := right A E B
  refine InvolutionTensorComparison.comparison_bijective B (D A E B) (baseSwap A E B σ)
    (baseSwap_involutive A E B σ hσ)
    (baseSwap_fixed_lifts A E B σ hσ hFixed h hHalfFixed hHalf)
    (i h) (i coefficient) (i u) (i v) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [baseSwap_right, hHalfFixed]
  · rw [← map_add, hHalf, map_one]
  · rw [baseSwap_right, hc]
  · rw [baseSwap_right, hu, map_neg]
  · rw [baseSwap_right, hv, map_neg]
  · simpa only [map_add, map_mul, map_pow, map_one] using congrArg (fun z : E => i z) hPartition

end

end ManuscriptAudit.InvolutionTensorBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.InvolutionTensorBaseChange.baseSwap_tmul,
        ``ManuscriptAudit.InvolutionTensorBaseChange.baseSwap_fixed_lifts,
        ``ManuscriptAudit.InvolutionTensorBaseChange.baseChange_comparison_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
