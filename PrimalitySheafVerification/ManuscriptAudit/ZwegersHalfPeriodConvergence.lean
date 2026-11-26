import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.ZwegersGaussianSummable
import PrimalitySheafVerification.ManuscriptAudit.ZwegersHalfPeriod

/-!
# Absolute convergence at the Zwegers half period

The norm of the actual bilateral correction term is the real Gaussian
majorant. This proves convergence on the upper half-plane for the same
kernel that gives the half-period cancellation.
-/

namespace ManuscriptAudit.ZwegersHalfPeriod

open ManuscriptAudit.ZwegersGaussianTail

noncomputable section

private theorem realSign_eq_sign (x : ℝ) : realSign x = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [realSign, hx.not_gt, hx.ne, Real.sign_of_neg hx]
  · simp [realSign]
  · simp [realSign, hx, Real.sign_of_pos hx]

private theorem gaussianPrimitive_eq_errorIntegral (x : ℝ) :
    gaussianPrimitive x = errorIntegral x := rfl

private theorem exponent_re (τ : ℂ) (u : ℝ) :
    (-((Real.pi : ℂ) * Complex.I) * (u : ℂ) ^ 2 * τ +
      ((Real.pi : ℂ) * Complex.I) * (u : ℂ)).re = Real.pi * τ.im * u ^ 2 := by
  rw [← Complex.ofReal_pow]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The norm of the manuscript's specialized kernel equals the real majorant. -/
theorem norm_kernelTerm (τ : ℂ) (n : ℤ) :
    ‖kernelTerm τ n‖ = weightedSignDefect τ.im (halfLattice n) := by
  let u := halfLattice n
  change ‖((realSign u - gaussianPrimitive (u * Real.sqrt (2 * τ.im)) : ℝ) : ℂ) *
    (-1 : ℂ) ^ n *
    Complex.exp (-((Real.pi : ℂ) * Complex.I) * (u : ℂ) ^ 2 * τ +
      ((Real.pi : ℂ) * Complex.I) * (u : ℂ))‖ = weightedSignDefect τ.im u
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_zpow, norm_neg,
    norm_one, one_zpow, mul_one, Complex.norm_exp, exponent_re, realSign_eq_sign,
    gaussianPrimitive_eq_errorIntegral, weightedSignDefect]

/-- The actual Zwegers correction at the real half period converges absolutely. -/
theorem summable_norm_kernelTerm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖kernelTerm τ n‖) := by
  simpa only [norm_kernelTerm, halfLattice] using
    (summable_weightedSignDefect_halfInteger hτ)

/-- The actual complex correction terms are summable on the upper half-plane. -/
theorem summable_kernelTerm {τ : ℂ} (hτ : 0 < τ.im) : Summable (kernelTerm τ) :=
  (summable_norm_kernelTerm hτ).of_norm

end

end ManuscriptAudit.ZwegersHalfPeriod

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ZwegersHalfPeriod.norm_kernelTerm,
      ``ManuscriptAudit.ZwegersHalfPeriod.summable_norm_kernelTerm,
      ``ManuscriptAudit.ZwegersHalfPeriod.summable_kernelTerm] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
