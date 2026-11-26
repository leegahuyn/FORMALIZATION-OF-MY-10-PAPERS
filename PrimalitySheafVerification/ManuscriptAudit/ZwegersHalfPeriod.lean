import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.Paper8XiShadow

/-!
# The Zwegers correction at the manuscript's real half period

Paper 8, Theorem 3.2, uses R(-1/2; τ) with arbitrary block coefficients.
At this real argument the sign character and elliptic exponential
multiply to a constant. The Gaussian sign difference is odd on the
half-lattice, so the two terms paired by n ↦ -n-1 cancel.

The formula for R is from Sander Zwegers, Mock Theta Functions, §1.4,
https://arxiv.org/abs/0807.4834. Lemma 1.8 proves absolute convergence
on the upper half-plane. The cancellation below is an identity of the
Lean bilateral sum itself.
-/

namespace ManuscriptAudit.ZwegersHalfPeriod

open MeasureTheory Paper8XiShadow
open MaassLaplacian (partialX partialY)

noncomputable section

def gaussianPrimitive (x : ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..x, Real.exp (-Real.pi * t ^ 2)

theorem gaussianPrimitive_neg (x : ℝ) :
    gaussianPrimitive (-x) = -gaussianPrimitive x := by
  let f (t : ℝ) := Real.exp (-Real.pi * t ^ 2)
  have h : (∫ t in (0 : ℝ)..x, f t) = ∫ t in -x..0, f t := by
    simpa only [f, neg_zero, neg_sq] using
      (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := x))
  change 2 * (∫ t in (0 : ℝ)..-x, f t) = -(2 * (∫ t in (0 : ℝ)..x, f t))
  rw [intervalIntegral.integral_symm (-x) 0, ← h]
  ring

def realSign (x : ℝ) : ℝ := if 0 < x then 1 else if x = 0 then 0 else -1

theorem realSign_neg (x : ℝ) : realSign (-x) = -realSign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hn : 0 < -x := neg_pos.mpr hx
    simp [realSign, hn, not_lt_of_gt hx, ne_of_lt hx]
  · simp [realSign]
  · have hn : -x < 0 := neg_lt_zero.mpr hx
    simp [realSign, hx, not_lt_of_gt hn, ne_of_lt hn]

def halfLattice (n : ℤ) : ℝ := (n : ℝ) + 1 / 2

theorem halfLattice_reflection (n : ℤ) : halfLattice (-n - 1) = -halfLattice n := by
  simp only [halfLattice, Int.cast_sub, Int.cast_neg, Int.cast_one]
  ring

private abbrev phaseUnit : ℂ := (Real.pi : ℂ) * Complex.I

/-- The literal summand of R(-1/2; τ), with a = Im(-1/2)/Im(τ) = 0. -/
def kernelTerm (τ : ℂ) (n : ℤ) : ℂ :=
  ((realSign (halfLattice n) -
      gaussianPrimitive (halfLattice n * Real.sqrt (2 * τ.im)) : ℝ) : ℂ) *
    (-1 : ℂ) ^ n *
    Complex.exp (-phaseUnit * (halfLattice n : ℂ) ^ 2 * τ +
      phaseUnit * (halfLattice n : ℂ))

private theorem halfLattice_cast (n : ℤ) :
    (halfLattice n : ℂ) = (n : ℂ) + 1 / 2 := by
  simp [halfLattice]

private theorem reduceCharacter (τ : ℂ) (n : ℤ) :
    (-1 : ℂ) ^ n *
      Complex.exp (-phaseUnit * (halfLattice n : ℂ) ^ 2 * τ +
        phaseUnit * (halfLattice n : ℂ)) =
    Complex.exp (-phaseUnit * (halfLattice n : ℂ) ^ 2 * τ) *
      Complex.exp (phaseUnit / 2) := by
  have hphase : phaseUnit * (halfLattice n : ℂ) =
      (n : ℂ) * phaseUnit + phaseUnit / 2 := by
    rw [halfLattice_cast]
    ring
  have hsquare : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_zpow]
    simp
  rw [hphase, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  calc
    _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
        (Complex.exp (-phaseUnit * (halfLattice n : ℂ) ^ 2 * τ) *
          Complex.exp (phaseUnit / 2)) := by ring
    _ = _ := by rw [hsquare, one_mul]

private theorem kernelTerm_eq_reduced (τ : ℂ) (n : ℤ) :
    kernelTerm τ n =
      ((realSign (halfLattice n) -
        gaussianPrimitive (halfLattice n * Real.sqrt (2 * τ.im)) : ℝ) : ℂ) *
      (Complex.exp (-phaseUnit * (halfLattice n : ℂ) ^ 2 * τ) *
        Complex.exp (phaseUnit / 2)) := by
  unfold kernelTerm
  rw [← reduceCharacter τ n]
  exact mul_assoc _ _ _

theorem kernelTerm_reflection (τ : ℂ) (n : ℤ) :
    kernelTerm τ (-n - 1) = -kernelTerm τ n := by
  have hOdd : realSign (halfLattice (-n - 1)) -
        gaussianPrimitive (halfLattice (-n - 1) * Real.sqrt (2 * τ.im)) =
      -(realSign (halfLattice n) -
        gaussianPrimitive (halfLattice n * Real.sqrt (2 * τ.im))) := by
    rw [halfLattice_reflection, realSign_neg, neg_mul, gaussianPrimitive_neg]
    ring
  have hSq : (halfLattice (-n - 1) : ℂ) ^ 2 = (halfLattice n : ℂ) ^ 2 := by
    rw [halfLattice_reflection, Complex.ofReal_neg, neg_sq]
  rw [kernelTerm_eq_reduced τ (-n - 1), kernelTerm_eq_reduced τ n, hOdd, hSq]
  simp only [Complex.ofReal_neg, neg_mul]

/-- The actual bilateral correction in the real half-period specialization. -/
def correction (τ : ℂ) : ℂ := ∑' n : ℤ, kernelTerm τ n

theorem correction_eq_zero (τ : ℂ) : correction τ = 0 := by
  let e : ℤ ≃ ℤ :=
    ⟨fun n => -n - 1, fun n => -n - 1,
      by
        intro n
        change -(-n - 1) - 1 = n
        omega,
      by
        intro n
        change -(-n - 1) - 1 = n
        omega⟩
  have h := e.tsum_eq (kernelTerm τ)
  have hfun : (fun n => kernelTerm τ (e n)) = fun n => -kernelTerm τ n :=
    funext (kernelTerm_reflection τ)
  change (∑' n, kernelTerm τ (e n)) = correction τ at h
  rw [hfun, tsum_neg] at h
  change -correction τ = correction τ at h
  have hsum := congrArg (fun z : ℂ => z + correction τ) h
  rw [neg_add_cancel, ← two_mul] at hsum
  exact (mul_eq_zero.mp hsum.symm).resolve_left two_ne_zero

/-- This correction contributes zero to the actual ξ operator. -/
theorem correction_xi_zero (x y : ℝ) :
    xiHalf (fun x y => correction (x + y * Complex.I)) x y = 0 := by
  have h : (fun x y : ℝ => correction (x + y * Complex.I)) = fun _ _ => 0 := by
    funext x y
    exact correction_eq_zero _
  rw [h]
  simp [xiHalf, dBar, partialX, partialY]

/-- No rescaling of this specialized correction supplies the nonzero printed shadow. -/
theorem correction_does_not_give_printedShadow (α κ : ℂ) (hκ : κ ≠ 0) :
    xiHalf (scale α (fun x y => correction (x + y * Complex.I))) 0 1 ≠
      κ * printedTheta Complex.I := by
  rw [xiHalf_scale, correction_xi_zero, mul_zero]
  exact (mul_ne_zero hκ printedTheta_at_I_ne_zero).symm

end

end ManuscriptAudit.ZwegersHalfPeriod

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ZwegersHalfPeriod.gaussianPrimitive_neg,
      ``ManuscriptAudit.ZwegersHalfPeriod.realSign_neg,
      ``ManuscriptAudit.ZwegersHalfPeriod.halfLattice_reflection,
      ``ManuscriptAudit.ZwegersHalfPeriod.kernelTerm_reflection,
      ``ManuscriptAudit.ZwegersHalfPeriod.correction_eq_zero,
      ``ManuscriptAudit.ZwegersHalfPeriod.correction_xi_zero,
      ``ManuscriptAudit.ZwegersHalfPeriod.correction_does_not_give_printedShadow] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
