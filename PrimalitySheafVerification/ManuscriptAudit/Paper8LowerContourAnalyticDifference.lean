import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalContourAtZero
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReflectedContourDifferenceBounds

/-!
# Signed fixed-radius contour difference near the inverse nome zero

The two reciprocal kernels have a uniformly summable difference on
the quarter disk. This is a statement about their difference series.
-/

namespace ManuscriptAudit.Paper8LowerContourAnalyticDifference

open Filter Metric Set
open scoped Topology
open Paper8ReciprocalContourAtZero (inverseNomeTerm
  reduced_inverseNomeTerm_zero_summable_and_positive all_inverseNomeTerm_zero_summable_and_positive)
open Paper8ContourResidueWeights (prefactor residueWeight reducedResidues)
open Paper8LocalContour (root)
open Paper8ContourDifferenceTerms (root_power_norm norm_weighted_le)
open Paper8ReflectedContourDifference (difference)
open Paper8ReflectedContourDifferenceBounds (difference_norm_le difference_sub_zero_norm_le)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos)
open Paper8ContourSignedDominance (decay decay_nonneg decay_tail_summable)
open Paper8ContourGammaRemainder (bound bound_nonneg)

noncomputable section

theorem inverseNomeTerm_eq_weighted_difference (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (Q : ℂ) :
    inverseNomeTerm S k Q =
      -(prefactor k * ∑ d ∈ S k, residueWeight k d *
        ((root k ^ (d.val : ℤ))⁻¹ * difference k (root k ^ (d.val : ℤ))⁻¹ Q)) := by
  have hNeg : -(46 / 3 : ℝ) = -46 / 3 := neg_div _ _
  simp only [inverseNomeTerm, difference, hNeg, neg_mul, mul_assoc]

private theorem inverse_root_norm (k : ℕ) (d : Fin (2 * k)) :
    ‖(root k ^ (d.val : ℤ))⁻¹‖ = 1 := by rw [norm_inv, root_power_norm, inv_one]

theorem inverseNomeTerm_norm_le (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k)
    {Q : ℂ} (hq : ‖Q‖ ≤ 1 / 4) :
    ‖inverseNomeTerm S k Q‖ ≤ (16 * fixedRadius * bound fixedRadius) * decay k := by
  rw [inverseNomeTerm_eq_weighted_difference, norm_neg]
  have hNonneg : 0 ≤ (8 * fixedRadius * bound fixedRadius) * decay k :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) fixedRadius_pos.le)
      (bound_nonneg fixedRadius_pos)) (decay_nonneg _)
  have h := norm_weighted_le hk (S k)
    (fun d => (root k ^ (d.val : ℤ))⁻¹ * difference k (root k ^ (d.val : ℤ))⁻¹ Q)
    hNonneg (fun d _ => by
      rw [norm_mul, inverse_root_norm, one_mul]
      exact difference_norm_le hk (inverse_root_norm k d) hq)
  refine h.trans_eq ?_
  ring

theorem inverseNomeTerm_sub_zero_norm_le (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k)
    {Q : ℂ} (hq : ‖Q‖ ≤ 1 / 4) :
    ‖inverseNomeTerm S k Q - inverseNomeTerm S k 0‖ ≤
      (32 * fixedRadius * bound fixedRadius) * decay k * ‖Q‖ := by
  have hEq : inverseNomeTerm S k Q - inverseNomeTerm S k 0 =
      -(prefactor k * ∑ d ∈ S k, residueWeight k d * ((root k ^ (d.val : ℤ))⁻¹ *
        (difference k (root k ^ (d.val : ℤ))⁻¹ Q - difference k (root k ^ (d.val : ℤ))⁻¹ 0))) := by
    let P (q : ℂ) := ∑ d ∈ S k, residueWeight k d *
      ((root k ^ (d.val : ℤ))⁻¹ * difference k (root k ^ (d.val : ℤ))⁻¹ q)
    rw [inverseNomeTerm_eq_weighted_difference S k Q, inverseNomeTerm_eq_weighted_difference S k 0]
    change -(prefactor k * P Q) - -(prefactor k * P 0) = _
    calc
      _ = -(prefactor k * (P Q - P 0)) := by ring
      _ = _ := by
        unfold P
        rw [← Finset.sum_sub_distrib]
        apply congrArg (fun w : ℂ => -(prefactor k * w))
        exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hEq, norm_neg]
  have hNonneg : 0 ≤ (16 * fixedRadius * bound fixedRadius) * decay k * ‖Q‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) fixedRadius_pos.le)
      (bound_nonneg fixedRadius_pos)) (decay_nonneg _)) (norm_nonneg _)
  have h := norm_weighted_le hk (S k)
    (fun d => (root k ^ (d.val : ℤ))⁻¹ *
      (difference k (root k ^ (d.val : ℤ))⁻¹ Q - difference k (root k ^ (d.val : ℤ))⁻¹ 0))
    hNonneg (fun d _ => by
      rw [norm_mul, inverse_root_norm, one_mul]
      exact difference_sub_zero_norm_le hk (inverse_root_norm k d) hq)
  refine h.trans_eq ?_
  ring

def normalizedDifference (S : ∀ k : ℕ, Finset (Fin (2 * k))) (Q : ℂ) : ℂ :=
  ∑' n : ℕ, inverseNomeTerm S (n + 1) Q

def outerDifference (S : ∀ k : ℕ, Finset (Fin (2 * k))) (Q : ℂ) : ℂ :=
  (Real.pi : ℂ) * normalizedDifference S Q

private theorem decay_all_summable : Summable (fun n : ℕ => decay (n + 1)) :=
  (summable_nat_add_iff 1).mp (decay_tail_summable 2 (by decide))

theorem absolute_summability_on_disk (S : ∀ k : ℕ, Finset (Fin (2 * k))) {Q : ℂ}
    (hq : ‖Q‖ ≤ 1 / 4) : Summable (fun n : ℕ => ‖inverseNomeTerm S (n + 1) Q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => inverseNomeTerm_norm_le S (Nat.succ_pos n) hq) (decay_all_summable.mul_left _)

theorem hasSumUniformlyOn_closed_disk (S : ∀ k : ℕ, Finset (Fin (2 * k))) :
    HasSumUniformlyOn (fun n Q => inverseNomeTerm S (n + 1) Q) (normalizedDifference S)
      (closedBall (0 : ℂ) (1 / 4)) :=
  HasSumUniformlyOn.of_norm_le_summable (f := fun n Q => inverseNomeTerm S (n + 1) Q)
    (decay_all_summable.mul_left (16 * fixedRadius * bound fixedRadius))
    (fun n _ hq => inverseNomeTerm_norm_le S (Nat.succ_pos n)
      (by simpa only [mem_closedBall, dist_zero_right] using hq))

private def modulusConstant : ℝ :=
  (32 * fixedRadius * bound fixedRadius) * (∑' n : ℕ, decay (n + 1))

private theorem modulusConstant_nonneg : 0 ≤ modulusConstant :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) fixedRadius_pos.le) (bound_nonneg fixedRadius_pos))
    (tsum_nonneg fun _ => decay_nonneg _)

theorem normalized_difference_norm_le (S : ∀ k : ℕ, Finset (Fin (2 * k))) {Q : ℂ}
    (hq : ‖Q‖ ≤ 1 / 4) :
    ‖normalizedDifference S Q - normalizedDifference S 0‖ ≤ modulusConstant * ‖Q‖ := by
  let C : ℝ := (32 * fixedRadius * bound fixedRadius) * ‖Q‖
  have hMajorant : Summable (fun n : ℕ => C * decay (n + 1)) := decay_all_summable.mul_left C
  have hNorm (n : ℕ) : ‖inverseNomeTerm S (n + 1) Q - inverseNomeTerm S (n + 1) 0‖ ≤
      C * decay (n + 1) := by
    have h := inverseNomeTerm_sub_zero_norm_le S (Nat.succ_pos n) hq
    convert h using 1 <;> unfold C <;> ring
  have hAbs : Summable (fun n : ℕ => ‖inverseNomeTerm S (n + 1) Q - inverseNomeTerm S (n + 1) 0‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hNorm hMajorant
  have h0 : ‖(0 : ℂ)‖ ≤ 1 / 4 := by norm_num
  unfold normalizedDifference
  rw [← (absolute_summability_on_disk S hq).of_norm.tsum_sub
    (absolute_summability_on_disk S h0).of_norm]
  calc
    _ ≤ ∑' n : ℕ, ‖inverseNomeTerm S (n + 1) Q - inverseNomeTerm S (n + 1) 0‖ :=
      norm_tsum_le_tsum_norm hAbs
    _ ≤ ∑' n : ℕ, C * decay (n + 1) := hAbs.tsum_le_tsum hNorm hMajorant
    _ = C * (∑' n : ℕ, decay (n + 1)) := tsum_mul_left
    _ = _ := by unfold C modulusConstant; ring

theorem normalized_continuousAt_zero (S : ∀ k : ℕ, Finset (Fin (2 * k))) :
    ContinuousAt (normalizedDifference S) 0 := by
  refine Metric.continuousAt_iff.mpr ?_
  intro ε hε
  let r : ℝ := min (1 / 4) (ε / (modulusConstant + 1))
  have hPos : 0 < modulusConstant + 1 := by linarith [modulusConstant_nonneg]
  refine ⟨r, lt_min (by norm_num) (div_pos hε hPos), ?_⟩
  intro Q hQ
  have hNorm : ‖Q‖ < r := by simpa only [dist_zero_right] using hQ
  have hq₁ : ‖Q‖ ≤ 1 / 4 := hNorm.le.trans (min_le_left _ _)
  have hq₂ : ‖Q‖ < ε / (modulusConstant + 1) := hNorm.trans_le (min_le_right _ _)
  rw [dist_eq_norm]
  calc
    _ ≤ modulusConstant * ‖Q‖ := normalized_difference_norm_le S hq₁
    _ ≤ (modulusConstant + 1) * ‖Q‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg Q)
    _ < (modulusConstant + 1) * (ε / (modulusConstant + 1)) :=
      mul_lt_mul_of_pos_left hq₂ hPos
    _ = _ := by rw [mul_comm, div_mul_cancel₀ _ hPos.ne']

theorem outerDifference_real_positive_near_zero (S : ∀ k : ℕ, Finset (Fin (2 * k)))
    (hSign : 0 < (normalizedDifference S 0).re) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∀ Q ∈ ball (0 : ℂ) r, 0 < (outerDifference S Q).re := by
  have h := Complex.continuous_re.continuousAt.comp (normalized_continuousAt_zero S)
  have hSet : {Q : ℂ | 0 < (normalizedDifference S Q).re} ∈ 𝓝 (0 : ℂ) :=
    h.tendsto (Ioi_mem_nhds hSign)
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hSet
  refine ⟨min r (1 / 4), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro Q hQ
  have hQ' : Q ∈ ball (0 : ℂ) r := by
    rw [mem_ball] at hQ ⊢
    exact hQ.trans_le (min_le_left _ _)
  have hQPos : 0 < (normalizedDifference S Q).re := hBall hQ'
  rw [outerDifference, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos Real.pi_pos hQPos

theorem reduced_outerDifference_real_positive_near_zero :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∀ Q ∈ ball (0 : ℂ) r, 0 < (outerDifference reducedResidues Q).re :=
  outerDifference_real_positive_near_zero reducedResidues reduced_inverseNomeTerm_zero_summable_and_positive.2

theorem all_outerDifference_real_positive_near_zero :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∀ Q ∈ ball (0 : ℂ) r,
      0 < (outerDifference (fun _ => Finset.univ) Q).re :=
  outerDifference_real_positive_near_zero (fun _ => Finset.univ) all_inverseNomeTerm_zero_summable_and_positive.2

end
end ManuscriptAudit.Paper8LowerContourAnalyticDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.inverseNomeTerm_eq_weighted_difference,
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.inverseNomeTerm_norm_le,
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.inverseNomeTerm_sub_zero_norm_le,
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.absolute_summability_on_disk,
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.hasSumUniformlyOn_closed_disk,
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.normalized_difference_norm_le,
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.normalized_continuousAt_zero,
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.reduced_outerDifference_real_positive_near_zero,
      ``ManuscriptAudit.Paper8LowerContourAnalyticDifference.all_outerDifference_real_positive_near_zero] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
