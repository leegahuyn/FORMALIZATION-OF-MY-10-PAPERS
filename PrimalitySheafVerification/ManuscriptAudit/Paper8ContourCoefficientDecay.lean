import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourMoment
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourSignedDominance

/-! Scaling of the actual difference of the two local q¹ coefficients in physical p. 335. -/

namespace ManuscriptAudit.Paper8ContourCoefficientDecay

open Paper8ContourGammaSeries (scale coefficient)
open Paper8ContourMomentTerm (coefficientMoment)
open Paper8ContourMoment (atZero hasSum_atZero_re atZero_literal_lt_rhoades)
open Paper8ContourSignedDominance (decay)

noncomputable section

def termDifference (k m : ℕ) : ℝ := coefficientMoment 23 k m - coefficientMoment (2 / 3) k m

def delta (k : ℕ) : ℝ := ∑' m : ℕ, termDifference k m

private theorem coefficient_nonneg (k m : ℕ) : 0 ≤ coefficient k m := by
  unfold coefficient
  have hScale : 0 ≤ scale k := by
    unfold scale
    exact div_nonneg Real.pi_pos.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  exact div_nonneg (Real.rpow_nonneg hScale _) (Real.Gamma_pos_of_pos (by positivity)).le

theorem termDifference_nonneg (k m : ℕ) : 0 ≤ termDifference k m := by
  unfold termDifference
  apply sub_nonneg.mpr
  unfold coefficientMoment
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (coefficient_nonneg k m)
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

theorem delta_nonneg (k : ℕ) : 0 ≤ delta k := tsum_nonneg (termDifference_nonneg k)

theorem hasSum_delta_eq_moments {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    HasSum (termDifference k) ((atZero 23 k r).re - (atZero (2 / 3) k r).re) :=
  (hasSum_atZero_re hk 23 hr).sub (hasSum_atZero_re hk (2 / 3) hr)

theorem delta_eq_moments {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    delta k = (atZero 23 k r).re - (atZero (2 / 3) k r).re :=
  (hasSum_delta_eq_moments hk hr).tsum_eq

theorem delta_one_pos : 0 < delta 1 := by
  rw [delta_eq_moments (by decide : 0 < (1 : ℕ)) (r := 1) zero_lt_one]
  exact sub_pos.mpr (atZero_literal_lt_rhoades (by decide : 0 < (1 : ℕ)) zero_lt_one)

private theorem scale_relation {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    scale k = scale j * ((j : ℝ) / (k : ℝ)) := by
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hj
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  unfold scale
  field_simp [hjR, hkR] <;> ring

private theorem coefficient_relation {j k : ℕ} (hj : 0 < j) (hk : 0 < k) (m : ℕ) :
    coefficient k m =
      ((j : ℝ) / (k : ℝ)) ^ (2 * (m : ℝ) + 1 / 2) * coefficient j m := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hScale : 0 ≤ scale j := by
    unfold scale
    positivity
  unfold coefficient
  rw [scale_relation hj hk, Real.mul_rpow hScale (div_nonneg hjR.le hkR.le)]
  ring

private theorem termDifference_relation {j k : ℕ} (hj : 0 < j) (hk : 0 < k) (m : ℕ) :
    termDifference k m =
      ((j : ℝ) / (k : ℝ)) ^ (2 * (m : ℝ) + 1 / 2) * termDifference j m := by
  unfold termDifference coefficientMoment
  rw [coefficient_relation hj hk m]
  ring

theorem termDifference_le_scaled {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) (m : ℕ) :
    termDifference k m ≤ ((j : ℝ) / (k : ℝ)) ^ (5 / 2 : ℝ) * termDifference j m := by
  have hk : 0 < k := hj.trans_le hjk
  by_cases h0 : m = 0
  · subst m
    simp [termDifference, coefficientMoment]
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hjkR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have hBase : (j : ℝ) / (k : ℝ) ≤ 1 := (div_le_one₀ hkR).2 hjkR
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  rw [termDifference_relation hj hk m]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge (div_pos hjR hkR) hBase (by linarith))
    (termDifference_nonneg j m)

theorem delta_le_scaled {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    delta k ≤ ((j : ℝ) / (k : ℝ)) ^ (5 / 2 : ℝ) * delta j := by
  have hJ := (hasSum_delta_eq_moments hj (r := 1) zero_lt_one).summable
  have hK := (hasSum_delta_eq_moments (hj.trans_le hjk) (r := 1) zero_lt_one).summable
  have h := hK.tsum_le_tsum (termDifference_le_scaled hj hjk)
    (hJ.mul_left (((j : ℝ) / (k : ℝ)) ^ (5 / 2 : ℝ)))
  rw [tsum_mul_left] at h
  exact h

theorem delta_le_decay {k : ℕ} (hk : 2 ≤ k) : delta k ≤ decay k * delta 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hDecay : ((1 : ℝ) / (k : ℝ)) ^ (5 / 2 : ℝ) = decay k := by
    unfold decay
    rw [Real.div_rpow zero_le_one hkR.le, Real.one_rpow,
      show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
      Real.rpow_add hkR, Real.rpow_two, ← Real.sqrt_eq_rpow]
  simpa only [Nat.cast_one, hDecay] using delta_le_scaled (by decide : 0 < (1 : ℕ)) (by omega : 1 ≤ k)

end
end ManuscriptAudit.Paper8ContourCoefficientDecay

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourCoefficientDecay.delta_nonneg,
      ``ManuscriptAudit.Paper8ContourCoefficientDecay.delta_eq_moments,
      ``ManuscriptAudit.Paper8ContourCoefficientDecay.delta_one_pos,
      ``ManuscriptAudit.Paper8ContourCoefficientDecay.termDifference_le_scaled,
      ``ManuscriptAudit.Paper8ContourCoefficientDecay.delta_le_scaled,
      ``ManuscriptAudit.Paper8ContourCoefficientDecay.delta_le_decay] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
