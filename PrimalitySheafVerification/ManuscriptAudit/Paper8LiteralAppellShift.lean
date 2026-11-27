import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8DiagonalEllipticLaw
import PrimalitySheafVerification.ManuscriptAudit.Paper8LiteralAppellPoint
import PrimalitySheafVerification.ManuscriptAudit.ZwegersHalfPeriodConvergence

/-!
# A nonzero literal p. 339 completion that fails the p. 340 shift law

The literal denominator on physical p. 339 is the even theta. Restrict
the printed completion to u − v = −1/2, so its actual correction is
the checked R(−1/2; τ). At the admissible sample point that correction
vanishes and the Appell quotient is nonzero. Under the simultaneous
τ shift the even-theta quotient changes sign. The p. 340 multiplier
at the same point is +4.
-/

namespace ManuscriptAudit.Paper8LiteralAppellShift

open AppellSameIntegerShift (numerator numerator_simultaneous_shift)
open Paper8LiteralAppellPoint
open Paper8DiagonalEllipticLaw (phase multiplier)
open ZwegersHalfPeriod (correction correction_eq_zero)

noncomputable section

private abbrev phaseUnit : ℂ := (Real.pi : ℂ) * Complex.I

def printedMu (u v τ : ℂ) : ℂ :=
  Complex.exp (phaseUnit * u) * numerator u v τ / jacobiTheta₂ v τ

def completedHalf (v τ : ℂ) : ℂ :=
  printedMu (v + sampleU) v τ + Complex.I / 2 * correction τ

theorem printedMu_diagonal_shift (u v τ : ℂ) :
    printedMu (u + τ) (v + τ) τ = -printedMu u v τ := by
  let b : ℂ := -(Real.pi : ℂ) * Complex.I * (τ + 2 * v)
  have hPhase : phaseUnit * (u + τ) + phaseUnit * (-2 * (τ + v) - 1) =
      (b + phaseUnit * u) + -phaseUnit := by dsimp [b]; ring
  have hExp : Complex.exp (phaseUnit * (u + τ)) *
        Complex.exp (phaseUnit * (-2 * (τ + v) - 1)) =
      -(Complex.exp b * Complex.exp (phaseUnit * u)) := by
    rw [← Complex.exp_add, hPhase, Complex.exp_add (b + phaseUnit * u), Complex.exp_add b,
      Complex.exp_neg_pi_mul_I, mul_neg_one]
  unfold printedMu
  rw [numerator_simultaneous_shift, jacobiTheta₂_add_left']
  change (Complex.exp (phaseUnit * (u + τ)) *
      (Complex.exp (phaseUnit * (-2 * (τ + v) - 1)) * numerator u v τ)) /
      (Complex.exp b * jacobiTheta₂ v τ) = _
  rw [← mul_assoc, hExp, neg_mul, neg_div, mul_assoc,
    mul_div_mul_left _ _ (Complex.exp_ne_zero b)]

theorem completedHalf_eq_mu (v τ : ℂ) : completedHalf v τ = printedMu (v + sampleU) v τ := by
  rw [completedHalf, correction_eq_zero, mul_zero, add_zero]

theorem completedHalf_diagonal_shift (v τ : ℂ) :
    completedHalf (v + τ) τ = -completedHalf v τ := by
  have h : v + τ + sampleU = (v + sampleU) + τ := by ring
  rw [completedHalf_eq_mu (v + τ) τ, completedHalf_eq_mu v τ, h, printedMu_diagonal_shift]

theorem sample_shifted_theta_ne_zero : jacobiTheta₂ sampleTau sampleTau ≠ 0 := by
  have h : jacobiTheta₂ sampleTau sampleTau =
      Complex.exp (-phaseUnit * sampleTau) * jacobiTheta₂ 0 sampleTau := by
    simpa only [zero_add, mul_zero, add_zero, neg_mul] using jacobiTheta₂_add_left' 0 sampleTau
  rw [h]
  exact mul_ne_zero (Complex.exp_ne_zero _) sample_theta_ne_zero

theorem sample_completedHalf_ne_zero : completedHalf 0 sampleTau ≠ 0 := by
  rw [completedHalf_eq_mu, zero_add, printedMu]
  exact div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) sample_numerator_ne_zero) sample_theta_ne_zero

theorem sample_printed_multiplier : multiplier sampleTau sampleU 0 1 0 = 4 := by
  have h : phase sampleTau sampleU 0 1 = -(phaseUnit * sampleTau) + phaseUnit := by
    simp only [phase, sampleU, Int.cast_one, one_pow, mul_one, add_zero]
    ring
  have hi : Complex.exp (-(phaseUnit * sampleTau)) = (4 : ℂ) := by
    rw [Complex.exp_neg, sample_half_nome]
    norm_num [Complex.ofReal_div]
  rw [multiplier, add_zero, zpow_one, h, Complex.exp_add, hi, Complex.exp_pi_mul_I]
  norm_num

/-- Both quotient denominators and all Appell pole denominators are nonzero
at this sample and at its diagonal translate. -/
theorem p340_literal_counterexample :
    completedHalf sampleTau sampleTau ≠
      multiplier sampleTau sampleU 0 1 0 * completedHalf 0 sampleTau := by
  have hShift : completedHalf sampleTau sampleTau = -completedHalf 0 sampleTau := by
    simpa only [zero_add] using completedHalf_diagonal_shift 0 sampleTau
  rw [hShift, sample_printed_multiplier]
  intro h
  have hz : (5 : ℂ) * completedHalf 0 sampleTau = 0 := by
    linear_combination -h
  exact (mul_ne_zero (by norm_num) sample_completedHalf_ne_zero) hz

end
end ManuscriptAudit.Paper8LiteralAppellShift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8LiteralAppellShift.printedMu_diagonal_shift,
      ``ManuscriptAudit.Paper8LiteralAppellShift.completedHalf_diagonal_shift,
      ``ManuscriptAudit.Paper8LiteralAppellShift.sample_shifted_theta_ne_zero,
      ``ManuscriptAudit.Paper8LiteralAppellShift.sample_completedHalf_ne_zero,
      ``ManuscriptAudit.Paper8LiteralAppellShift.sample_printed_multiplier,
      ``ManuscriptAudit.Paper8LiteralAppellShift.p340_literal_counterexample] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
