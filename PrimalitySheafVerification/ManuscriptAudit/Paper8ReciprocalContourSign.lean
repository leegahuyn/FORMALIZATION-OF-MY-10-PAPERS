import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalContourMoment
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourDifferenceTerms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourAllResidueTail

/-! Strict signed lower inverse-nome constant term comparison in physical p. 335. -/

namespace ManuscriptAudit.Paper8ReciprocalContourSign

open Paper8ReciprocalContourMoment (magnitude momentDifference momentDifference_bounds magnitude_first_le_decay)
open Paper8ContourGammaSeries (coefficient coefficient_pos)
open Paper8ContourResidueWeights
  (prefactor residueWeight weighted reducedResidues reducedWeight reducedWeight_one allWeight allWeight_one)
open Paper8LocalContour (root)
open Paper8ContourDifferenceTerms (root_power_norm norm_weighted_le)
open Paper8ContourSignedDominance (decay decay_nonneg decay_tail_summable)
open Paper8ContourAllResidueTail (scaled_tail_three_lt)

noncomputable section

def inverseWeight (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) : ℂ :=
  prefactor k * ∑ d ∈ S k, residueWeight k d * (root k ^ (d.val : ℤ))⁻¹

private theorem inverseWeight_norm_le (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) :
    ‖inverseWeight S k‖ ≤ 2 := by
  have h := norm_weighted_le hk (S k) (fun d => (root k ^ (d.val : ℤ))⁻¹)
    (c := 1) zero_le_one (fun d _ => by rw [norm_inv, root_power_norm]; norm_num)
  simpa only [inverseWeight, mul_one] using h

private theorem oneResidues : reducedResidues 1 = ({1} : Finset (Fin 2)) := by decide

private theorem weight1 : residueWeight 1 (1 : Fin 2) = -1 := by
  have h := reducedWeight_one
  rw [reducedWeight, weighted, oneResidues, Finset.sum_singleton] at h
  norm_num [prefactor] at h
  first
  | exact h
  | linear_combination -h
  | linear_combination h

private theorem weight0 : residueWeight 1 (0 : Fin 2) = 1 := by
  have h := allWeight_one
  rw [allWeight, weighted, Fin.sum_univ_two, weight1] at h
  norm_num [prefactor] at h
  first
  | exact h
  | linear_combination -h
  | linear_combination h

private theorem root1 : root 1 = -1 := by
  simpa only [root, Nat.cast_one, div_one] using Complex.exp_pi_mul_I

theorem inverseWeight_reduced_one : inverseWeight reducedResidues 1 = -1 := by
  rw [inverseWeight, oneResidues, Finset.sum_singleton, weight1, root1]
  norm_num [prefactor]

theorem inverseWeight_all_one : inverseWeight (fun _ => Finset.univ) 1 = -2 := by
  change prefactor 1 * (∑ d : Fin 2, residueWeight 1 d * (root 1 ^ (d.val : ℤ))⁻¹) = -2
  rw [Fin.sum_univ_two, weight0, weight1, root1]
  norm_num [prefactor]

theorem decay_tail_two_lt_three_eighths :
    (∑' n : ℕ, decay (n + 2)) < 3 / 8 := by
  have hSqrt : (7 / 5 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hThree : (∑' n : ℕ, decay (n + 3)) < 6 / 35 := by
    have hSum : 0 ≤ ∑' n : ℕ, decay (n + 3) := tsum_nonneg (fun _ => decay_nonneg _)
    have hLo := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSqrt (by norm_num : (0 : ℝ) ≤ 8)) hSum
    linarith only [scaled_tail_three_lt, hLo]
  have hTwo : decay 2 ≤ 5 / 28 := by
    change 1 / ((2 : ℝ) ^ 2 * Real.sqrt 2) ≤ 5 / 28
    calc
      _ ≤ 1 / ((2 : ℝ) ^ 2 * (7 / 5)) :=
        one_div_le_one_div_of_le (by norm_num)
          (mul_le_mul_of_nonneg_left hSqrt (by norm_num))
      _ = _ := by norm_num
  rw [(decay_tail_summable 2 (by decide)).tsum_eq_zero_add]
  change decay 2 + (∑' n : ℕ, decay (n + 3)) < 3 / 8
  linarith

def signedMoment (S : ∀ k : ℕ, Finset (Fin (2 * k))) (r : ℝ) (n : ℕ) : ℂ :=
  -inverseWeight S (n + 1) * (momentDifference (n + 1) r : ℂ)

private theorem firstMagnitude_pos : 0 < magnitude 1 0 := by
  unfold magnitude
  refine div_pos (mul_pos (coefficient_pos (k := 1) (by decide) 1) ?_) ?_ <;> norm_num

theorem signedMoment_summable_and_real_positive (S : ∀ k : ℕ, Finset (Fin (2 * k))) {r : ℝ}
    (hr : 0 < r) (hFirst : (inverseWeight S 1).re ≤ -1) :
    Summable (fun n : ℕ => ‖signedMoment S r n‖) ∧
      0 < (∑' n : ℕ, signedMoment S r n).re := by
  let T := signedMoment S r
  have hNonneg (k : ℕ) (hk : 0 < k) : 0 ≤ momentDifference k r := by
    have hb := (momentDifference_bounds hk hr).1
    have hm : 0 ≤ magnitude k 0 := by
      unfold magnitude
      refine div_nonneg (mul_nonneg (coefficient_pos hk 1).le ?_) ?_ <;> norm_num
    exact (mul_nonneg (by norm_num) hm).trans hb
  have hMaj : Summable (fun n => (2 * magnitude 1 0) * decay (n + 2)) :=
    (decay_tail_summable 2 (by decide)).mul_left _
  have hNorm (n : ℕ) : ‖T (n + 1)‖ ≤ (2 * magnitude 1 0) * decay (n + 2) := by
    have hk : 0 < n + 2 := by omega
    change ‖-inverseWeight S (n + 2) * (momentDifference (n + 2) r : ℂ)‖ ≤ _
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (hNonneg _ hk)]
    calc
      _ ≤ 2 * (decay (n + 2) * magnitude 1 0) :=
        mul_le_mul (inverseWeight_norm_le S hk)
          ((momentDifference_bounds hk hr).2.trans (magnitude_first_le_decay hk))
          (hNonneg _ hk) (by norm_num)
      _ = _ := by ring
  have hAbs : Summable (fun n => ‖T (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hNorm hMaj
  have hSum : Summable (fun n => ‖T n‖) := (summable_nat_add_iff 1).mp hAbs
  have hTail : ‖∑' n : ℕ, T (n + 1)‖ < (3 / 4) * magnitude 1 0 := by
    calc
      _ ≤ ∑' n : ℕ, ‖T (n + 1)‖ := norm_tsum_le_tsum_norm hAbs
      _ ≤ ∑' n : ℕ, (2 * magnitude 1 0) * decay (n + 2) := hAbs.tsum_le_tsum hNorm hMaj
      _ = (2 * magnitude 1 0) * (∑' n : ℕ, decay (n + 2)) := tsum_mul_left
      _ < (2 * magnitude 1 0) * (3 / 8 : ℝ) :=
        mul_lt_mul_of_pos_left decay_tail_two_lt_three_eighths (mul_pos (by norm_num) firstMagnitude_pos)
      _ = _ := by ring
  have hLeading : (3 / 4) * magnitude 1 0 ≤ (T 0).re := by
    change _ ≤ (-inverseWeight S 1 * (momentDifference 1 r : ℂ)).re
    rw [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ momentDifference 1 r := (momentDifference_bounds (by decide) hr).1
      _ = 1 * momentDifference 1 r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hFirst]) (hNonneg 1 (by decide))
  refine ⟨hSum, ?_⟩
  change 0 < (∑' n : ℕ, T n).re
  rw [hSum.of_norm.tsum_eq_zero_add, Complex.add_re]
  have hLower : -‖∑' n : ℕ, T (n + 1)‖ ≤ (∑' n : ℕ, T (n + 1)).re :=
    (neg_le_neg (Complex.abs_re_le_norm _)).trans (neg_abs_le _)
  linarith only [hLeading, hTail, hLower]

theorem reduced_signedMoment_summable_and_real_positive {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => ‖signedMoment reducedResidues r n‖) ∧
      0 < (∑' n : ℕ, signedMoment reducedResidues r n).re :=
  signedMoment_summable_and_real_positive reducedResidues hr (by rw [inverseWeight_reduced_one]; norm_num)

theorem all_signedMoment_summable_and_real_positive {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => ‖signedMoment (fun _ => Finset.univ) r n‖) ∧
      0 < (∑' n : ℕ, signedMoment (fun _ => Finset.univ) r n).re :=
  signedMoment_summable_and_real_positive (fun _ => Finset.univ) hr (by rw [inverseWeight_all_one]; norm_num)

end
end ManuscriptAudit.Paper8ReciprocalContourSign

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReciprocalContourSign.inverseWeight_reduced_one,
      ``ManuscriptAudit.Paper8ReciprocalContourSign.inverseWeight_all_one,
      ``ManuscriptAudit.Paper8ReciprocalContourSign.decay_tail_two_lt_three_eighths,
      ``ManuscriptAudit.Paper8ReciprocalContourSign.signedMoment_summable_and_real_positive,
      ``ManuscriptAudit.Paper8ReciprocalContourSign.reduced_signedMoment_summable_and_real_positive,
      ``ManuscriptAudit.Paper8ReciprocalContourSign.all_signedMoment_summable_and_real_positive] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
