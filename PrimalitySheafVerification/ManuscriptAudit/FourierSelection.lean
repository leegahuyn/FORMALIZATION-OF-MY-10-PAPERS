import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# Fourier selection in Paper 8, physical PDF p. 366

Lemma 5 prints a product of two positive Fourier phases. The ordinary
x-integral selects n+m=0. This calculation is termwise and leaves unfolding,
exchange of the sums and integrals, and the later central-value comparison
to their separate analytic proofs.
-/

namespace ManuscriptAudit.FourierSelection

private theorem integral_integerPhase (k : ℤ) :
    (∫ x : ℝ in 0..1,
      Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))) =
      if k = 0 then (1 : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hc : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hk)
        (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero)
    rw [integral_exp_mul_complex hc]
    simp [hk, Complex.exp_int_mul_two_pi_mul_I]

/-- Two positive phases are selected by the sum of their integer frequencies. -/
theorem integral_positiveFourierProduct (n m : ℤ) :
    (∫ x : ℝ in 0..1,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x : ℂ))) =
      if n + m = 0 then (1 : ℂ) else 0 := by
  calc
    _ = (∫ x : ℝ in 0..1,
        Complex.exp (((n + m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [← Complex.exp_add, Int.cast_add]
      congr 1
      ring
    _ = _ := integral_integerPhase (n + m)

/-- The same selection holds for the printed phases at `τ=x+iy` for fixed `y`. -/
theorem integral_positiveFourierProduct_at_height (n m : ℤ) (y : ℝ) :
    (∫ x : ℝ in 0..1,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))) =
      if n + m = 0 then (1 : ℂ) else 0 := by
  let c : ℂ := ((n + m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  calc
    _ = (∫ x : ℝ in 0..1,
        Complex.exp (c * ((y : ℂ) * Complex.I)) * Complex.exp (c * (x : ℂ))) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [c, ← Complex.exp_add, Int.cast_add]
      congr 1
      ring
    _ = Complex.exp (c * ((y : ℂ) * Complex.I)) *
        (if n + m = 0 then (1 : ℂ) else 0) := by
      rw [intervalIntegral.integral_const_mul]
      change Complex.exp (c * ((y : ℂ) * Complex.I)) *
        (∫ x : ℝ in 0..1, Complex.exp
          (((n + m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ))) = _
      rw [integral_integerPhase]
    _ = _ := by
      by_cases h : n + m = 0
      · simp [c, h]
      · simp [h]

/-- The positive diagonal pair n=m=1 has zero x-integral at every height. -/
theorem integral_samePositiveUnitMode_zero (y : ℝ) :
    (∫ x : ℝ in 0..1,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x : ℂ) + (y : ℂ) * Complex.I)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x : ℂ) + (y : ℂ) * Complex.I))) = 0 := by
  have h : (1 : ℤ) + 1 ≠ 0 := by decide
  simpa only [Int.cast_one, mul_one, if_neg h] using
    integral_positiveFourierProduct_at_height 1 1 y

end ManuscriptAudit.FourierSelection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.FourierSelection.integral_positiveFourierProduct,
    ``ManuscriptAudit.FourierSelection.integral_positiveFourierProduct_at_height,
    ``ManuscriptAudit.FourierSelection.integral_samePositiveUnitMode_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
