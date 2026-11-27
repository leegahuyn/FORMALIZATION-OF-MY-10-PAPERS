import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8HolomorphicPartPhase

/-!
# The literal diagonal elliptic law on physical p. 340

The formula shifts both arguments by the same `λτ + μ` and multiplies by
`(-1)^(λ+μ) exp(-πiλ²τ - 2πiλ(u+v))`. Applying the shift with `λ=1`
twice introduces a different scalar from applying `λ=2` directly.
Consequently the printed law forces a function to vanish at every point
whose diagonal translate is also covered by the law.
-/

namespace ManuscriptAudit.Paper8DiagonalEllipticLaw

open Paper8HolomorphicPartPhase (periodCoefficient qParameter qParameter_norm_lt_one)

noncomputable section

def phase (τ u v : ℂ) (λ : ℤ) : ℂ :=
  -(Real.pi : ℂ) * Complex.I * (λ : ℂ) ^ 2 * τ -
    2 * (Real.pi : ℂ) * Complex.I * (λ : ℂ) * (u + v)

def multiplier (τ u v : ℂ) (λ μ : ℤ) : ℂ :=
  (-1 : ℂ) ^ (λ + μ) * Complex.exp (phase τ u v λ)

private theorem multiplier_one (τ u v : ℂ) :
    multiplier τ u v 1 0 = -Complex.exp (phase τ u v 1) := by
  simp only [multiplier, add_zero, zpow_one, neg_one_mul]

private theorem multiplier_two (τ u v : ℂ) :
    multiplier τ u v 2 0 = Complex.exp (phase τ u v 2) := by
  rw [multiplier, add_zero, show (-1 : ℂ) ^ (2 : ℤ) = 1 by norm_num, one_mul]

private theorem phase_two_steps (τ u v : ℂ) :
    phase τ (u + τ) (v + τ) 1 + phase τ u v 1 =
      phase τ u v 2 + -(periodCoefficient * τ) := by
  simp only [phase, periodCoefficient, Int.cast_one, Int.cast_ofNat]
  ring

/-- The extra factor is exactly the reciprocal of the upper-half-plane parameter. -/
theorem multiplier_two_steps (τ u v : ℂ) :
    multiplier τ (u + τ) (v + τ) 1 0 * multiplier τ u v 1 0 =
      multiplier τ u v 2 0 * (qParameter τ)⁻¹ := by
  rw [multiplier_one τ (u + τ) (v + τ), multiplier_one τ u v, multiplier_two,
    neg_mul_neg, ← Complex.exp_add, phase_two_steps, Complex.exp_add, Complex.exp_neg, qParameter]

private theorem inverse_parameter_ne_one {τ : ℂ} (hτ : 0 < τ.im) :
    (qParameter τ)⁻¹ ≠ 1 := by
  intro h
  have hOne : qParameter τ = 1 := by
    simpa only [inv_inv, inv_one] using congrArg (fun z : ℂ => z⁻¹) h
  simpa only [hOne, norm_one, lt_irrefl] using qParameter_norm_lt_one hτ

theorem value_zero_of_literal_steps {F : ℂ → ℂ → ℂ} {τ u v : ℂ} (hτ : 0 < τ.im)
    (hOne : F (u + τ) (v + τ) = multiplier τ u v 1 0 * F u v)
    (hNext : F ((u + τ) + τ) ((v + τ) + τ) =
      multiplier τ (u + τ) (v + τ) 1 0 * F (u + τ) (v + τ))
    (hTwo : F (u + 2 * τ) (v + 2 * τ) = multiplier τ u v 2 0 * F u v) :
    F u v = 0 := by
  have hIterated : F (u + 2 * τ) (v + 2 * τ) =
      (multiplier τ u v 2 0 * (qParameter τ)⁻¹) * F u v := by
    calc
      _ = F ((u + τ) + τ) ((v + τ) + τ) := by
        have hu : u + 2 * τ = (u + τ) + τ := by ring
        have hv : v + 2 * τ = (v + τ) + τ := by ring
        exact congrArg₂ F hu hv
      _ = _ := by rw [hNext, hOne, ← mul_assoc, multiplier_two_steps]
  by_contra hValue
  have hMult : multiplier τ u v 2 0 = multiplier τ u v 2 0 * (qParameter τ)⁻¹ :=
    mul_right_cancel₀ hValue (hTwo.symm.trans hIterated)
  have hNonzero : multiplier τ u v 2 0 ≠ 0 := by
    rw [multiplier_two]
    exact Complex.exp_ne_zero _
  apply inverse_parameter_ne_one hτ
  exact mul_left_cancel₀ hNonzero (by simpa only [mul_one] using hMult.symm)

theorem literal_diagonal_elliptic_law_forces_zero {τ : ℂ} (hτ : 0 < τ.im)
    (D : ℂ → ℂ → Prop) (F : ℂ → ℂ → ℂ)
    (hClosed : ∀ u v, D u v → D (u + τ) (v + τ))
    (hLaw : ∀ u v, D u v → ∀ λ μ : ℤ,
      F (u + (λ : ℂ) * τ + (μ : ℂ)) (v + (λ : ℂ) * τ + (μ : ℂ)) =
        multiplier τ u v λ μ * F u v) :
    ∀ u v, D u v → F u v = 0 := by
  intro u v hD
  apply value_zero_of_literal_steps hτ
  · simpa only [Int.cast_one, one_mul, Int.cast_zero, add_zero] using hLaw u v hD 1 0
  · simpa only [Int.cast_one, one_mul, Int.cast_zero, add_zero] using
      hLaw (u + τ) (v + τ) (hClosed u v hD) 1 0
  · simpa only [Int.cast_ofNat, Int.cast_zero, add_zero] using hLaw u v hD 2 0

end
end ManuscriptAudit.Paper8DiagonalEllipticLaw

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DiagonalEllipticLaw.multiplier_two_steps,
      ``ManuscriptAudit.Paper8DiagonalEllipticLaw.value_zero_of_literal_steps,
      ``ManuscriptAudit.Paper8DiagonalEllipticLaw.literal_diagonal_elliptic_law_forces_zero] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
