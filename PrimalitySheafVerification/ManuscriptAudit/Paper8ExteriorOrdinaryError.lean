import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorOrdinaryTelescope
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorOrdinaryCorrection

/-! The two exact recurrences give the normalized error equation. -/

namespace ManuscriptAudit.Paper8ExteriorOrdinaryError

open Paper8ExteriorOrdinarySums Paper8ExteriorOrdinaryTelescope Paper8ExteriorOrdinaryCorrection
open Paper8EulerianRecurrence (H H_recurrence)

noncomputable section

def rawError (q a : ℝ) : ℝ :=
  J q a + a * C q a - (1 + a) * W q a * H q a

def normalizedError (q a : ℝ) : ℝ :=
  D q a + a * C q a / W q a - (1 + a) * H q a

def multiplier (q a : ℝ) : ℝ := a ^ 3 * q ^ 2 * (1 + a) / (1 + a * q)

private theorem W_scaled_shift {q a : ℝ} (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) :
    a * (1 + a * q) * W q (a * q) = (1 + a) * W q a := by
  have hInv : a * (1 + a⁻¹) = 1 + a := by field_simp [ha.ne'] <;> ring
  calc
    _ = a * ((1 + a * q) * W q (a * q)) := by ring
    _ = _ := by rw [W_shift hq h₁ ha, ← mul_assoc, hInv]

theorem rawError_recurrence {q a : ℝ} (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) (ha₁ : a ≤ 1) :
    rawError q a = a ^ 4 * q ^ 2 * rawError q (a * q) := by
  have hJ := J_recurrence hq h₁ ha
  have hC := C_recurrence hq.le h₁ ha.le ha₁
  have hH := H_recurrence hq.le h₁ ha.le ha₁
  have hW := W_scaled_shift hq h₁ ha
  unfold rawError
  linear_combination hJ + a * hC - ((1 + a) * W q a) * hH + (a ^ 3 * q ^ 2 * H q (a * q)) * hW

private theorem rawError_eq_W_mul_normalized {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) :
    rawError q a = W q a * normalizedError q a := by
  have hW : W q a ≠ 0 := (zero_lt_one.trans_le (one_le_W hq h₁ ha)).ne'
  rw [rawError, normalizedError, J_eq_W_mul_D hq h₁ ha]
  field_simp [hW] <;> ring

theorem normalizedError_recurrence {q a : ℝ}
    (hq : 0 < q) (h₁ : q < 1) (ha : 0 < a) (ha₁ : a ≤ 1) :
    normalizedError q a = multiplier q a * normalizedError q (a * q) := by
  have hW : W q a ≠ 0 := (zero_lt_one.trans_le (one_le_W hq.le h₁ ha.le)).ne'
  have hRaw := rawError_recurrence hq h₁ ha ha₁
  rw [rawError_eq_W_mul_normalized hq.le h₁ ha.le,
    rawError_eq_W_mul_normalized hq.le h₁ (mul_nonneg ha.le hq.le)] at hRaw
  have hMult : a ^ 4 * q ^ 2 * W q (a * q) = W q a * multiplier q a := by
    rw [multiplier, mul_div_assoc]
    apply (eq_div_iff (by positivity : 1 + a * q ≠ 0)).mpr
    linear_combination (a ^ 3 * q ^ 2) * (W_scaled_shift hq h₁ ha)
  apply mul_left_cancel₀ hW
  calc
    _ = a ^ 4 * q ^ 2 * (W q (a * q) * normalizedError q (a * q)) := hRaw
    _ = (a ^ 4 * q ^ 2 * W q (a * q)) * normalizedError q (a * q) := by ring
    _ = (W q a * multiplier q a) * normalizedError q (a * q) := by rw [hMult]
    _ = _ := by ring

theorem multiplier_nonneg {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) : 0 ≤ multiplier q a := by
  unfold multiplier
  positivity

theorem multiplier_le_q {q a : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    multiplier q a ≤ q := by
  have hA : a ^ 3 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ ha ha₁ 3
  have hQ : q ^ 2 ≤ q := by
    rw [pow_two]
    exact mul_le_of_le_one_right hq h₁
  unfold multiplier
  apply (div_le_iff₀ (by positivity : 0 < 1 + a * q)).mpr
  calc
    _ ≤ (1 : ℝ) * q ^ 2 * (1 + a) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA (sq_nonneg q)) (by positivity)
    _ ≤ _ := by nlinarith only [hQ]

end
end ManuscriptAudit.Paper8ExteriorOrdinaryError

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorOrdinaryError.rawError_recurrence,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryError.normalizedError_recurrence,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryError.multiplier_le_q] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
