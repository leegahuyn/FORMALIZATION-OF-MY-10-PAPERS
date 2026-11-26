import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import PrimalitySheafVerification.ManuscriptAudit.ZwegersGaussianTail

/-!
# Summability of the Zwegers Gaussian majorant

At a real half-period the error-integral argument is scaled by √(2v),
where v is the positive imaginary part of the upper half-plane parameter.
The Gaussian tail absorbs the growth factor exp(πvν²) at every
half-integer ν.
-/

namespace ManuscriptAudit.ZwegersGaussianTail

noncomputable section

/-- The absolute sign defect multiplied by the growth of the complex Gaussian factor. -/
def weightedSignDefect (v u : ℝ) : ℝ :=
  |Real.sign u - errorIntegral (u * Real.sqrt (2 * v))| * Real.exp (Real.pi * v * u ^ 2)

private theorem weightedSignDefect_neg (v u : ℝ) :
    weightedSignDefect v (-u) = weightedSignDefect v u := by
  unfold weightedSignDefect
  have h : Real.sign (-u) - errorIntegral ((-u) * Real.sqrt (2 * v)) =
      -(Real.sign u - errorIntegral (u * Real.sqrt (2 * v))) := by
    rw [Real.sign_neg, neg_mul, errorIntegral_neg]
    ring
  rw [h, abs_neg, neg_sq]

private theorem weightedSignDefect_le {v u : ℝ} (hv : 0 < v) (hu : 1 / 2 ≤ u) :
    weightedSignDefect v u ≤
      2 / (Real.pi * Real.sqrt (2 * v)) * Real.exp (-Real.pi * v * u ^ 2) := by
  let s := Real.sqrt (2 * v)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsSq : s ^ 2 = 2 * v := Real.sq_sqrt (by positivity)
  have hu' : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hus : 0 < u * s := mul_pos hu' hs
  have hA := sign_sub_errorIntegral_abs_le (u * s) hus.ne'
  rw [Real.sign_of_pos hus, abs_of_pos hus] at hA
  have hExp :
      Real.exp (-Real.pi * (u * s) ^ 2) * Real.exp (Real.pi * v * u ^ 2) =
        Real.exp (-Real.pi * v * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [mul_pow, hsSq]
    ring
  have hInv : (Real.pi * (u * s))⁻¹ ≤ 2 / (Real.pi * s) := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (mul_pos Real.pi_pos hus) (mul_pos Real.pi_pos hs)).2
    have hnn : 0 ≤ 2 * u - 1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hs.le) hnn]
  change |Real.sign u - errorIntegral (u * s)| * Real.exp (Real.pi * v * u ^ 2) ≤
    2 / (Real.pi * s) * Real.exp (-Real.pi * v * u ^ 2)
  rw [Real.sign_of_pos hu']
  calc
    _ ≤ (Real.exp (-Real.pi * (u * s) ^ 2) / (Real.pi * (u * s))) *
        Real.exp (Real.pi * v * u ^ 2) :=
      mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
    _ = Real.exp (-Real.pi * v * u ^ 2) / (Real.pi * (u * s)) := by
      rw [div_mul_eq_mul_div, hExp]
    _ ≤ _ := by
      rw [div_eq_mul_inv,
        mul_comm (Real.exp (-Real.pi * v * u ^ 2)) ((Real.pi * (u * s))⁻¹)]
      exact mul_le_mul_of_nonneg_right hInv (Real.exp_nonneg _)

/-- The real majorant for the Zwegers correction is summable along the half-integers. -/
theorem summable_weightedSignDefect_halfInteger {v : ℝ} (hv : 0 < v) :
    Summable (fun k : ℤ => weightedSignDefect v ((k : ℝ) + 1 / 2)) := by
  have hc : -Real.pi * v < 0 := mul_neg_of_neg_of_pos (neg_lt_zero.2 Real.pi_pos) hv
  have hG : Summable (fun n : ℕ => Real.exp (-Real.pi * v * ((n : ℝ) + 1 / 2) ^ 2)) :=
    Real.summable_exp_nat_mul_of_ge hc (by
      intro n
      nlinarith [sq_nonneg (n : ℝ)])
  have hPos : Summable (fun n : ℕ => weightedSignDefect v ((n : ℝ) + 1 / 2)) := by
    refine (hG.mul_left (2 / (Real.pi * Real.sqrt (2 * v)))).of_nonneg_of_le ?_ ?_
    · intro n
      exact mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
    · intro n
      exact weightedSignDefect_le hv (le_add_of_nonneg_left (Nat.cast_nonneg n))
  apply Summable.of_nat_of_neg_add_one
  · simpa only [Int.cast_natCast] using hPos
  · have hCast (n : ℕ) : (((-(n + 1 : ℤ)) : ℤ) : ℝ) + 1 / 2 = -((n : ℝ) + 1 / 2) := by
      push_cast
      ring
    simpa only [hCast, weightedSignDefect_neg] using hPos

end

end ManuscriptAudit.ZwegersGaussianTail

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ZwegersGaussianTail.summable_weightedSignDefect_halfInteger
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
