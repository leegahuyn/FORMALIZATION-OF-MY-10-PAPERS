import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorOrdinaryError
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianDictionary

/-!
# The corrected p. 335 ordinary exterior identity on the positive radius

The bounded normalized error satisfies a contraction, so the squared
denominator and actual product correction give the minus-sign identity.
-/

namespace ManuscriptAudit.Paper8ExteriorOrdinaryDictionary

open Filter
open Paper8ExteriorOrdinarySums Paper8ExteriorOrdinaryCorrection Paper8ExteriorOrdinaryError
open Paper8EulerianRecurrence (H H_abs_le_geometric)
open Paper8EulerianPentagonal (H_one_eq_pentagonalSeries)
open Paper8EulerianDictionary (unilateralTheta_eq_pentagonalSeries)
open Paper8ExteriorNormalization (ramanujanF)
open Paper8ExteriorProductCorrection (unilateralTheta productCorrection)

open scoped Topology

theorem normalizedError_abs_bound {q a : ℝ}
    (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) (ha₁ : a ≤ 1) :
    |normalizedError q a| ≤ 4 * (1 - q)⁻¹ := by
  have hW := one_le_W hq.le h₁ ha.le
  have hD := D_abs_le_geometric hq.le h₁ ha.le
  have hC := C_abs_le_geometric hq.le h₁ ha.le ha₁
  have hH := H_abs_le_geometric hq.le h₁ ha.le ha₁
  have hCorr : |a * C q a / W q a| ≤ (1 - q)⁻¹ := by
    rw [abs_div, abs_mul, abs_of_pos ha, abs_of_nonneg (zero_le_one.trans hW)]
    calc
      _ ≤ a * |C q a| := div_le_self (mul_nonneg ha.le (abs_nonneg _)) hW
      _ ≤ 1 * |C q a| := mul_le_mul_of_nonneg_right ha₁ (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hC
  have hHScale : |(1 + a) * H q a| ≤ 2 * (1 - q)⁻¹ := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + a)]
    exact mul_le_mul (by linarith only [ha₁]) hH (abs_nonneg _) (by norm_num)
  have hAdd : |D q a + a * C q a / W q a| ≤ |D q a| + |a * C q a / W q a| :=
    by simpa only [Real.norm_eq_abs] using norm_add_le (D q a) (a * C q a / W q a)
  have hSub : |normalizedError q a| ≤ |D q a + a * C q a / W q a| + |(1 + a) * H q a| :=
    by simpa only [Real.norm_eq_abs, normalizedError] using
      norm_sub_le (D q a + a * C q a / W q a) ((1 + a) * H q a)
  linarith only [hD, hCorr, hHScale, hAdd, hSub]

theorem normalizedError_abs_le_pow {q a : ℝ}
    (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) (ha₁ : a ≤ 1) (N : ℕ) :
    |normalizedError q a| ≤ q ^ N * (4 * (1 - q)⁻¹) := by
  induction N generalizing a with
  | zero => simpa only [pow_zero, one_mul] using normalizedError_abs_bound hq h₁ ha ha₁
  | succ N ih =>
      have hAQ : a * q ≤ 1 := by
        calc
          _ ≤ a * 1 := mul_le_mul_of_nonneg_left h₁.le ha.le
          _ ≤ _ := by simpa only [mul_one] using ha₁
      calc
        _ = multiplier q a * |normalizedError q (a * q)| := by
          rw [normalizedError_recurrence hq h₁ ha ha₁, abs_mul,
            abs_of_nonneg (multiplier_nonneg hq.le ha.le)]
        _ ≤ q * (q ^ N * (4 * (1 - q)⁻¹)) :=
          mul_le_mul (multiplier_le_q hq.le h₁.le ha.le ha₁)
            (ih (mul_pos ha hq) hAQ) (abs_nonneg _) hq.le
        _ = _ := by rw [pow_succ' q N, mul_assoc]

theorem normalizedError_zero {q a : ℝ}
    (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) (ha₁ : a ≤ 1) :
    normalizedError q a = 0 := by
  have hLimit : Tendsto (fun N : ℕ => q ^ N * (4 * (1 - q)⁻¹)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le h₁).mul_const (4 * (1 - q)⁻¹)
  have hNonpos : |normalizedError q a| ≤ 0 :=
    ge_of_tendsto hLimit (Eventually.of_forall (normalizedError_abs_le_pow hq h₁ ha ha₁))
  exact abs_eq_zero.mp (le_antisymm hNonpos (abs_nonneg _))

theorem p335_unweighted_exterior_corrected {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    ramanujanF q⁻¹ = 2 * unilateralTheta q - productCorrection q := by
  have h := normalizedError_zero hq h₁ (a := 1) (by norm_num) le_rfl
  have hH : H q 1 = unilateralTheta q :=
    (H_one_eq_pentagonalSeries hq.le h₁).trans (unilateralTheta_eq_pentagonalSeries hq h₁).symm
  rw [normalizedError, D_one_eq_literal_exterior hq, C_one_eq_literal_numerator,
    W_one_eq_correction_denominator, hH] at h
  unfold productCorrection
  norm_num only [one_mul, one_add_one_eq_two] at h
  linarith only [h]

end ManuscriptAudit.Paper8ExteriorOrdinaryDictionary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorOrdinaryDictionary.normalizedError_abs_bound,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryDictionary.normalizedError_abs_le_pow,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryDictionary.normalizedError_zero,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryDictionary.p335_unweighted_exterior_corrected] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
