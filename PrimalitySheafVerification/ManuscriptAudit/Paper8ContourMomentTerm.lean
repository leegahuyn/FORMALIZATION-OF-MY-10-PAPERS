import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourGammaSeries
import PrimalitySheafVerification.ManuscriptAudit.Paper8HolomorphicPartPhase

/-! Native termwise contour moments for the p. 335 Laurent series. -/

namespace ManuscriptAudit.Paper8ContourMomentTerm

open Paper8ContourGammaSeries (coefficient term)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Metric

noncomputable section

def weightedTerm (α : ℝ) (k m : ℕ) (s : ℂ) : ℂ :=
  term k m s * Complex.exp ((α : ℂ) * s)

def coefficientMoment (α : ℝ) (k m : ℕ) : ℝ := coefficient k m * α ^ m / m.factorial

theorem periodCoefficient_ne_zero : periodCoefficient ≠ 0 := by
  unfold periodCoefficient
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

theorem weightedTerm_circle_integral (α : ℝ) (k m : ℕ) {r : ℝ} (hr : 0 < r) :
    periodCoefficient⁻¹ * circleIntegral (weightedTerm α k m) 0 r =
      (coefficientMoment α k m : ℂ) := by
  let f : ℂ → ℂ := fun s => Complex.exp ((α : ℂ) * s)
  have hd : DifferentiableOn ℂ f (closedBall (0 : ℂ) r) :=
    (Complex.differentiable_exp.comp
      ((differentiable_const (c := (α : ℂ))).mul differentiable_id)).differentiableOn
  have hC := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hr m hd
  have hTerm : weightedTerm α k m = fun s : ℂ =>
      (coefficient k m : ℂ) * ((1 / (s - 0) ^ (m + 1)) • f s) := by
    funext s
    simp only [weightedTerm, term, sub_zero, smul_eq_mul, div_eq_mul_inv, one_mul, f, mul_assoc]
  rw [hTerm, circleIntegral.integral_const_mul, hC]
  change periodCoefficient⁻¹ * ((coefficient k m : ℂ) *
    ((periodCoefficient / (m.factorial : ℂ)) * iteratedDeriv m f 0)) = _
  simp only [f, Complex.iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one,
    coefficientMoment, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  have hFact : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp [periodCoefficient_ne_zero, hFact] <;> ring

end
end ManuscriptAudit.Paper8ContourMomentTerm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourMomentTerm.periodCoefficient_ne_zero,
      ``ManuscriptAudit.Paper8ContourMomentTerm.weightedTerm_circle_integral] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
