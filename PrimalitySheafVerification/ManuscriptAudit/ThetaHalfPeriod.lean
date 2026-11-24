import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic.Ring

/-!
# The printed theta denominator in Paper 8

Physical PDF p. 350, G.1, defines the uncharacteristic theta series
`∑ₙ exp(π i n²τ + 2π i n z)` and divides by its value at `1/2 + τ/2`.
Its value there is zero throughout the upper half-plane. The declarations
below use precisely this two-variable series and its genuine convergent sum.
They concern the p. 350 denominator, independently of the p. 305 Appell
numerator and the character theta series defined later in the paper.
-/

namespace ManuscriptAudit.ThetaHalfPeriod

theorem paper_theta_halfPeriod_eq_zero (τ : ℂ) :
    jacobiTheta₂ (1 / 2 + τ / 2) τ = 0 := by
  let z : ℂ := 1 / 2 + τ / 2
  change jacobiTheta₂ z τ = 0
  have hz : 2 * z = 1 + τ := by
    dsimp only [z]
    rw [mul_add, mul_comm (2 : ℂ) (1 / 2), mul_comm (2 : ℂ) (τ / 2),
      div_mul_cancel₀ (1 : ℂ) two_ne_zero, div_mul_cancel₀ τ two_ne_zero]
  have hperiodIndex : (-z + τ) + 1 = z := by
    calc
      (-z + τ) + 1 = (1 + τ) - z := by ring
      _ = z := by rw [← hz]; ring
  have hinner : τ + 2 * (-z) = -1 := by
    rw [mul_neg, hz]
    ring
  have hphase : -(Real.pi : ℂ) * Complex.I * (τ + 2 * (-z)) =
      (Real.pi : ℂ) * Complex.I := by
    rw [hinner]
    ring
  have hperiod := jacobiTheta₂_add_left (-z + τ) τ
  rw [hperiodIndex] at hperiod
  have hshift := jacobiTheta₂_add_left' (-z) τ
  rw [hphase, Complex.exp_pi_mul_I, jacobiTheta₂_neg_left, neg_one_mul] at hshift
  have hanti : jacobiTheta₂ z τ = -jacobiTheta₂ z τ := hperiod.trans hshift
  have hsum : jacobiTheta₂ z τ + jacobiTheta₂ z τ = 0 :=
    (congrArg (fun w : ℂ => w + jacobiTheta₂ z τ) hanti).trans (neg_add_cancel _)
  rw [← two_mul] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left two_ne_zero

/-- The actual bilateral series printed at this argument has sum zero. -/
theorem hasSum_paper_theta_denominator_zero (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ +
        2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1 / 2 + τ / 2))) 0 := by
  have hs := hasSum_jacobiTheta₂_term (1 / 2 + τ / 2) hτ
  rw [paper_theta_halfPeriod_eq_zero] at hs
  simpa only [jacobiTheta₂_term, Int.cast_pow, add_comm] using hs

/-- There is no reciprocal for the denominator used in the printed quotient. -/
theorem paper_theta_denominator_has_no_reciprocal (τ : ℂ) (hτ : 0 < τ.im) :
    ¬ ∃ r : ℂ, r * (∑' n : ℤ,
      Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * τ +
        2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1 / 2 + τ / 2))) = 1 := by
  rw [(hasSum_paper_theta_denominator_zero τ hτ).tsum_eq]
  simp

end ManuscriptAudit.ThetaHalfPeriod

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.ThetaHalfPeriod.paper_theta_halfPeriod_eq_zero,
    ``ManuscriptAudit.ThetaHalfPeriod.hasSum_paper_theta_denominator_zero,
    ``ManuscriptAudit.ThetaHalfPeriod.paper_theta_denominator_has_no_reciprocal] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
