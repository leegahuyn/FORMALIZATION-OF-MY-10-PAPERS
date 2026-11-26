import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Ring

/-!
# A tensor product criterion for a two-element action

If two anti-invariant elements have squares generating one via
invariant coefficients, the two multiplication maps give the
Galois comparison. The proof constructs its inverse on tensors.
-/

namespace ManuscriptAudit.InvolutionTensorComparison

open scoped TensorProduct

noncomputable section

variable (A E : Type*) [CommRing A] [CommRing E] [Algebra A E]

private abbrev left : E →+* (E ⊗[A] E) := algebraMap E (E ⊗[A] E)
private abbrev right : E →ₐ[A] (E ⊗[A] E) := Algebra.TensorProduct.includeRight

local notation "ι₁" => left A E
local notation "ι₂" => right A E

private def evaluate (f : E →ₐ[A] E) : (E ⊗[A] E) →ₐ[E] E :=
  Algebra.TensorProduct.lift (AlgHom.id E E) f (fun _ _ => Commute.all _ _)

private theorem evaluate_tmul (f : E →ₐ[A] E) (a b : E) :
    evaluate A E f (a ⊗ₜ[A] b) = a * f b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

private theorem evaluate_left (f : E →ₐ[A] E) (a : E) :
    evaluate A E f (ι₁ a) = a :=
  (evaluate A E f).commutes a

private theorem evaluate_right (f : E →ₐ[A] E) (a : E) :
    evaluate A E f (ι₂ a) = f a := by
  rw [Algebra.TensorProduct.includeRight_apply, evaluate_tmul, one_mul]

private theorem left_eq_right {z : E} (h : ∃ a : A, algebraMap A E a = z) :
    ι₁ z = ι₂ z := by
  obtain ⟨a, rfl⟩ := h
  rw [← IsScalarTower.algebraMap_apply A E (E ⊗[A] E) a, (right A E).commutes]

/-- The canonical multiplication and twisted multiplication pair. -/
def comparison (σ : E ≃ₐ[A] E) : (E ⊗[A] E) →ₐ[E] (E × E) :=
  (evaluate A E (AlgHom.id A E)).prod (evaluate A E σ.toAlgHom)

theorem comparison_tmul (σ : E ≃ₐ[A] E) (a b : E) :
    comparison A E σ (a ⊗ₜ[A] b) = (a * b, a * σ b) := by
  apply Prod.ext
  · exact evaluate_tmul A E (AlgHom.id A E) a b
  · exact evaluate_tmul A E σ.toAlgHom a b

private theorem tensor_partition_mul_difference (σ : E ≃ₐ[A] E)
    (hInvol : Function.Involutive σ)
    (hFixed : ∀ z : E, σ z = z → ∃ a : A, algebraMap A E a = z)
    (λ₀ u v : E) (hλ : σ λ₀ = λ₀) (hu : σ u = -u) (hv : σ v = -v)
    (hPartition : λ₀ * u ^ 2 + v ^ 2 = 1) (b : E) :
    (ι₁ λ₀ * ι₁ u * ι₂ u + ι₁ v * ι₂ v) * ι₁ (b - σ b) = ι₂ (b - σ b) := by
  let d := b - σ b
  have hd : σ d = -d := by
    dsimp [d]
    rw [map_sub, hInvol b]
    ring
  have hShiftU : ι₁ (u * d) = ι₂ (u * d) :=
    left_eq_right A E (hFixed _ (by rw [map_mul, hu, hd, neg_mul_neg]))
  have hShiftV : ι₁ (v * d) = ι₂ (v * d) :=
    left_eq_right A E (hFixed _ (by rw [map_mul, hv, hd, neg_mul_neg]))
  change (ι₁ λ₀ * ι₁ u * ι₂ u + ι₁ v * ι₂ v) * ι₁ d = ι₂ d
  calc
    _ = ι₁ λ₀ * ι₁ (u * d) * ι₂ u + ι₁ (v * d) * ι₂ v := by
      simp only [map_mul]
      ring
    _ = ι₂ λ₀ * ι₂ (u * d) * ι₂ u + ι₂ (v * d) * ι₂ v := by
      rw [left_eq_right A E (hFixed λ₀ hλ), hShiftU, hShiftV]
    _ = ι₂ ((λ₀ * u ^ 2 + v ^ 2) * d) := by
      simp only [map_mul, map_add, map_pow]
      ring
    _ = _ := by rw [hPartition, one_mul]

set_option maxHeartbeats 1200000 in
theorem comparison_bijective (σ : E ≃ₐ[A] E)
    (hInvol : Function.Involutive σ)
    (hFixed : ∀ z : E, σ z = z → ∃ a : A, algebraMap A E a = z)
    (h λ₀ u v : E) (hHalfFixed : σ h = h) (hHalf : h + h = 1)
    (hλ : σ λ₀ = λ₀) (hu : σ u = -u) (hv : σ v = -v)
    (hPartition : λ₀ * u ^ 2 + v ^ 2 = 1) :
    Function.Bijective (comparison A E σ) := by
  let μ := evaluate A E (AlgHom.id A E)
  let ν := evaluate A E σ.toAlgHom
  let w : E ⊗[A] E := ι₁ λ₀ * ι₁ u * ι₂ u + ι₁ v * ι₂ v
  let e : E ⊗[A] E := ι₁ h * (1 + w)
  have hμl (a : E) : μ (ι₁ a) = a := evaluate_left A E _ a
  have hνl (a : E) : ν (ι₁ a) = a := evaluate_left A E _ a
  have hμr (a : E) : μ (ι₂ a) = a := evaluate_right A E _ a
  have hνr (a : E) : ν (ι₂ a) = σ a := evaluate_right A E _ a
  have hμw : μ w = 1 := by
    simpa only [w, map_add, map_mul, hμl, hμr, pow_two, mul_assoc] using hPartition
  have hνw : ν w = -1 := by
    calc
      ν w = -(λ₀ * u ^ 2 + v ^ 2) := by
        simp only [w, map_add, map_mul, hνl, hνr, hu, hv]
        ring
      _ = _ := by rw [hPartition]
  have hμe : μ e = 1 := by
    rw [e, map_mul, map_add, map_one, hμl, hμw, mul_add, mul_one, hHalf]
  have hνe : ν e = 0 := by
    simp only [e, map_mul, map_add, map_one, hνl, hνw, add_neg_cancel, mul_zero]
  have hHalfLeft : ι₁ h + ι₁ h = 1 := by rw [← map_add, hHalf, map_one]
  have hHalfRight : ι₂ h + ι₂ h = 1 := by rw [← map_add, hHalf, map_one]
  have hRight (b : E) : ι₂ b = ι₁ b * e + ι₁ (σ b) * (1 - e) := by
    have hSum : σ (b + σ b) = b + σ b := by
      rw [map_add, hInvol b]
      exact add_comm _ _
    have hw : w * ι₁ (b - σ b) = ι₂ (b - σ b) :=
      tensor_partition_mul_difference A E σ hInvol hFixed λ₀ u v hλ hu hv hPartition b
    calc
      ι₂ b = ι₂ h * (ι₂ (b + σ b) + ι₂ (b - σ b)) := by
        symm
        simp only [map_add, map_sub]
        calc
          _ = (ι₂ h + ι₂ h) * ι₂ b := by ring
          _ = _ := by rw [hHalfRight, one_mul]
      _ = ι₁ h * (ι₁ (b + σ b) + w * ι₁ (b - σ b)) := by
        rw [left_eq_right A E (hFixed h hHalfFixed),
          left_eq_right A E (hFixed _ hSum), hw]
      _ = ι₁ (b - σ b) * e + (ι₁ h + ι₁ h) * ι₁ (σ b) := by
        simp only [e, map_add, map_sub]
        ring
      _ = _ := by
        rw [hHalfLeft, one_mul]
        simp only [map_sub]
        ring
  have hμtmul (a b : E) : μ (a ⊗ₜ[A] b) = a * b := evaluate_tmul A E _ a b
  have hνtmul (a b : E) : ν (a ⊗ₜ[A] b) = a * σ b := evaluate_tmul A E _ a b
  have reconstruct (z : E ⊗[A] E) : z = ι₁ (μ z) * e + ι₁ (ν z) * (1 - e) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      calc
        a ⊗ₜ[A] b = ι₁ a * ι₂ b := by
          change _ = (a ⊗ₜ[A] 1) * (1 ⊗ₜ[A] b)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        _ = _ := by
          rw [hRight b, hμtmul, hνtmul]
          simp only [map_mul]
          ring
    | add a b ha hb =>
      calc
        a + b = (ι₁ (μ a) * e + ι₁ (ν a) * (1 - e)) +
            (ι₁ (μ b) * e + ι₁ (ν b) * (1 - e)) := congrArg₂ (· + ·) ha hb
        _ = _ := by
          simp only [map_add]
          ring
  constructor
  · intro z z' hz
    have h₁ : μ z = μ z' := congrArg Prod.fst hz
    have h₂ : ν z = ν z' := congrArg Prod.snd hz
    exact (reconstruct z).trans (by rw [h₁, h₂, ← reconstruct z'])
  · rintro ⟨a, b⟩
    refine ⟨ι₁ a * e + ι₁ b * (1 - e), Prod.ext ?_ ?_⟩
    · change μ (ι₁ a * e + ι₁ b * (1 - e)) = a
      simp only [map_add, map_mul, map_sub, map_one, hμl, hμe, sub_self, mul_one, mul_zero, add_zero]
    · change ν (ι₁ a * e + ι₁ b * (1 - e)) = b
      simp only [map_add, map_mul, map_sub, map_one, hνl, hνe, sub_zero, mul_one, mul_zero, zero_add]

end

end ManuscriptAudit.InvolutionTensorComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.InvolutionTensorComparison.comparison_tmul,
        ``ManuscriptAudit.InvolutionTensorComparison.comparison_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
