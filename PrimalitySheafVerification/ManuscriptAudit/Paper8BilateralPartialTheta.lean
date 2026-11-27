import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8BilateralKroneckerShadow
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorProductCorrection

/-!
# The bilateral partial-theta expression on physical p. 314 cancels

With the specified Kronecker symbol, the bilateral expression on this
page has an odd summand. The positive-index partial theta on p. 335 has a
different value at the same explicit test argument.
-/

namespace ManuscriptAudit.Paper8BilateralPartialTheta

open Paper8BilateralKroneckerShadow (kronecker_at_neg)
open Paper8ExteriorNormalization (partialThetaTerm partialTheta partialTheta_summable_abs)
open Paper8ExteriorProductCorrection (unilateralTheta testQ unilateralTheta_testQ_ge)

theorem partialThetaTerm_odd (q : ℝ) (n : ℤ) :
    partialThetaTerm q (-n) = -partialThetaTerm q n := by
  simp only [partialThetaTerm, kronecker_at_neg, Int.cast_neg, neg_sq, neg_mul]

theorem p314_bilateral_hasSum_zero {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    HasSum (partialThetaTerm q) 0 := by
  have hNorm : Summable (fun n : ℤ => ‖partialThetaTerm q n‖) := by
    simpa only [Real.norm_eq_abs] using partialTheta_summable_abs hq h₁
  have hSum : Summable (partialThetaTerm q) := hNorm.of_norm
  have hZero : partialThetaTerm q 0 = 0 := by
    simp [partialThetaTerm, Paper8ExteriorNormalization.kroneckerNegTwelve]
  have hPair : (fun n : ℕ => partialThetaTerm q (n : ℤ) + partialThetaTerm q (-(n : ℤ))) =
      (0 : ℕ → ℝ) := by
    funext n
    rw [partialThetaTerm_odd]
    exact add_neg_cancel _
  have hPaired := hSum.hasSum.nat_add_neg
  rw [hPair, hZero, add_zero] at hPaired
  have hTotal : (∑' n : ℤ, partialThetaTerm q n) = 0 := hPaired.unique hasSum_zero
  exact hTotal ▸ hSum.hasSum

theorem p314_bilateral_ne_p335_unilateral :
    partialTheta testQ ≠ unilateralTheta testQ := by
  have hq : 0 < testQ := by norm_num [testQ]
  have h₁ : testQ < 1 := by norm_num [testQ]
  rw [partialTheta, (p314_bilateral_hasSum_zero hq h₁).tsum_eq]
  exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5 / 6) unilateralTheta_testQ_ge).ne

end ManuscriptAudit.Paper8BilateralPartialTheta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8BilateralPartialTheta.partialThetaTerm_odd,
      ``ManuscriptAudit.Paper8BilateralPartialTheta.p314_bilateral_hasSum_zero,
      ``ManuscriptAudit.Paper8BilateralPartialTheta.p314_bilateral_ne_p335_unilateral] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
