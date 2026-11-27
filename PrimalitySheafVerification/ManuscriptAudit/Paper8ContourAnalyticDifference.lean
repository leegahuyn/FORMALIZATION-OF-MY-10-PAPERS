import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Slope
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourDifferenceTerms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourAllResidueSign

/-!
# The signed contour difference has the extracted first derivative

The difference of the actual local kernels is summable on the fixed
q-disk, after the common Laurent term cancels. Its value at q=0 is the
extracted signed coefficient. The derivative of the full difference
with the outer q factor therefore has the computed strict signs.
-/

namespace ManuscriptAudit.Paper8ContourAnalyticDifference

open Filter Metric Set
open Paper8ContourDifferenceTerms (term term_at_zero term_norm_le term_sub_zero_norm_le)
open Paper8ContourResidueWeights (weighted reducedResidues reducedWeight allWeight)
open Paper8ContourCoefficientDecay (delta)
open Paper8ContourSignedDominance (decay decay_nonneg decay_tail_summable)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos)
open Paper8ContourGammaRemainder (bound bound_nonneg)
open Paper8ContourSignedCoefficient (reduced_difference_summable_and_positive)
open Paper8ContourAllResidueSign (all_difference_real_negative)
open scoped Topology

noncomputable section

def normalizedDifference (S : ∀ k : ℕ, Finset (Fin (2 * k))) (q : ℂ) : ℂ :=
  ∑' n : ℕ, term S (n + 1) q

def outerDifference (S : ∀ k : ℕ, Finset (Fin (2 * k))) (q : ℂ) : ℂ :=
  (Real.pi : ℂ) * q * normalizedDifference S q

private theorem decay_all_summable : Summable (fun n : ℕ => decay (n + 1)) :=
  (summable_nat_add_iff 1).mp (decay_tail_summable 2 (by decide))

theorem absolute_summability_on_disk (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 4) : Summable (fun n : ℕ => ‖term S (n + 1) q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => term_norm_le S (Nat.succ_pos n) hq) (decay_all_summable.mul_left _)

theorem hasSumUniformlyOn_closed_disk (S : ∀ k : ℕ, Finset (Fin (2 * k))) :
    HasSumUniformlyOn (fun n q => term S (n + 1) q) (normalizedDifference S)
      (closedBall (0 : ℂ) (1 / 4)) :=
  HasSumUniformlyOn.of_norm_le_summable (f := fun n q => term S (n + 1) q)
    (decay_all_summable.mul_left (16 * fixedRadius * bound fixedRadius))
    (fun n _ hq => term_norm_le S (Nat.succ_pos n)
      (by simpa only [mem_closedBall, dist_zero_right] using hq))

theorem normalized_at_zero (S : ∀ k : ℕ, Finset (Fin (2 * k))) :
    normalizedDifference S 0 = ∑' n : ℕ, weighted (n + 1) (S (n + 1)) * (delta (n + 1) : ℂ) := by
  unfold normalizedDifference
  exact tsum_congr fun n => term_at_zero S (Nat.succ_pos n)

private def modulusConstant : ℝ :=
  (32 * fixedRadius * bound fixedRadius) * (∑' n : ℕ, decay (n + 1))

private theorem modulusConstant_nonneg : 0 ≤ modulusConstant :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) fixedRadius_pos.le) (bound_nonneg fixedRadius_pos))
    (tsum_nonneg fun _ => decay_nonneg _)

theorem normalized_difference_norm_le (S : ∀ k : ℕ, Finset (Fin (2 * k))) {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 4) :
    ‖normalizedDifference S q - normalizedDifference S 0‖ ≤ modulusConstant * ‖q‖ := by
  let C : ℝ := (32 * fixedRadius * bound fixedRadius) * ‖q‖
  have hMajorant : Summable (fun n : ℕ => C * decay (n + 1)) := decay_all_summable.mul_left C
  have hNorm (n : ℕ) : ‖term S (n + 1) q - term S (n + 1) 0‖ ≤ C * decay (n + 1) := by
    have h := term_sub_zero_norm_le S (Nat.succ_pos n) hq
    convert h using 1 <;> unfold C <;> ring
  have hAbs : Summable (fun n : ℕ => ‖term S (n + 1) q - term S (n + 1) 0‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hNorm hMajorant
  have h0 : ‖(0 : ℂ)‖ ≤ 1 / 4 := by norm_num
  unfold normalizedDifference
  rw [← (absolute_summability_on_disk S hq).of_norm.tsum_sub
    (absolute_summability_on_disk S h0).of_norm]
  calc
    _ ≤ ∑' n : ℕ, ‖term S (n + 1) q - term S (n + 1) 0‖ := norm_tsum_le_tsum_norm hAbs
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
  intro q hq
  have hNorm : ‖q‖ < r := by simpa only [dist_zero_right] using hq
  have hq₁ : ‖q‖ ≤ 1 / 4 := hNorm.le.trans (min_le_left _ _)
  have hq₂ : ‖q‖ < ε / (modulusConstant + 1) := hNorm.trans_le (min_le_right _ _)
  rw [dist_eq_norm]
  calc
    _ ≤ modulusConstant * ‖q‖ := normalized_difference_norm_le S hq₁
    _ ≤ (modulusConstant + 1) * ‖q‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg q)
    _ < (modulusConstant + 1) * (ε / (modulusConstant + 1)) :=
      mul_lt_mul_of_pos_left hq₂ hPos
    _ = _ := by rw [mul_comm, div_mul_cancel₀ _ hPos.ne']

theorem outer_hasDerivAt_zero (S : ∀ k : ℕ, Finset (Fin (2 * k))) :
    HasDerivAt (outerDifference S) ((Real.pi : ℂ) * normalizedDifference S 0) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hC : ContinuousAt (fun q : ℂ => (Real.pi : ℂ) * normalizedDifference S q) 0 :=
    continuousAt_const.mul (normalized_continuousAt_zero S)
  have hT : Tendsto (fun q : ℂ => (Real.pi : ℂ) * normalizedDifference S q)
      (𝓝[≠] (0 : ℂ)) (𝓝 ((Real.pi : ℂ) * normalizedDifference S 0)) :=
    hC.tendsto.mono_left nhdsWithin_le_nhds
  apply hT.congr'
  have hP : ({0}ᶜ : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := self_mem_nhdsWithin
  filter_upwards [hP] with q hq
  have hq0 : q ≠ 0 := by
    intro he
    change q ∉ ({0} : Set ℂ) at hq
    apply hq
    simpa only [Set.mem_singleton_iff] using he
  simp only [outerDifference, zero_add, mul_zero, zero_mul, sub_zero, smul_eq_mul]
  field_simp [hq0] <;> ring

theorem reduced_derivative_real_positive :
    0 < (deriv (outerDifference reducedResidues) 0).re := by
  rw [(outer_hasDerivAt_zero reducedResidues).deriv, normalized_at_zero,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos Real.pi_pos reduced_difference_summable_and_positive.2

theorem all_derivative_real_negative :
    (deriv (outerDifference (fun _ => Finset.univ)) 0).re < 0 := by
  rw [(outer_hasDerivAt_zero (fun _ => Finset.univ)).deriv, normalized_at_zero,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg Real.pi_pos all_difference_real_negative

private theorem small_positive_real_sign (S : ∀ k : ℕ, Finset (Fin (2 * k))) (c : ℝ)
    (hSign : 0 < c * (normalizedDifference S 0).re) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Ioo (0 : ℝ) r, 0 < c * (outerDifference S (x : ℂ)).re := by
  have hRe : ContinuousAt (fun q : ℂ => (normalizedDifference S q).re) 0 :=
    Complex.continuous_re.continuousAt.comp (normalized_continuousAt_zero S)
  have hCont : ContinuousAt (fun q : ℂ => c * (normalizedDifference S q).re) 0 :=
    continuousAt_const.mul hRe
  have hSet : {q : ℂ | 0 < c * (normalizedDifference S q).re} ∈ 𝓝 (0 : ℂ) :=
    hCont.tendsto (Ioi_mem_nhds hSign)
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp hSet
  refine ⟨min r (1 / 4), lt_min hr (by norm_num), ?_⟩
  intro x hx
  have hx' : 0 < x := hx.1
  have hX : (x : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hx'.le]
    exact hx.2.trans_le (min_le_left _ _)
  have hXSign : 0 < c * (normalizedDifference S (x : ℂ)).re := hBall hX
  have hMul : (Real.pi : ℂ) * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) :=
    (Complex.ofReal_mul _ _).symm
  rw [outerDifference, hMul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    0 < (Real.pi * x) * (c * (normalizedDifference S (x : ℂ)).re) :=
      mul_pos (mul_pos Real.pi_pos hx') hXSign
    _ = _ := by ring

theorem reduced_difference_positive_for_small_positive_q :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Ioo (0 : ℝ) r, 0 < (outerDifference reducedResidues (x : ℂ)).re := by
  have h : 0 < (normalizedDifference reducedResidues 0).re := by
    rw [normalized_at_zero]
    exact reduced_difference_summable_and_positive.2
  simpa only [one_mul] using small_positive_real_sign reducedResidues 1 (by simpa using h)

theorem all_difference_negative_for_small_positive_q :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Ioo (0 : ℝ) r,
      (outerDifference (fun _ => Finset.univ) (x : ℂ)).re < 0 := by
  have h : (normalizedDifference (fun _ => Finset.univ) 0).re < 0 := by
    rw [normalized_at_zero]
    exact all_difference_real_negative
  simpa only [neg_one_mul, neg_pos] using
    small_positive_real_sign (fun _ => Finset.univ) (-1) (by simpa using neg_pos.mpr h)

end
end ManuscriptAudit.Paper8ContourAnalyticDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.absolute_summability_on_disk,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.hasSumUniformlyOn_closed_disk,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.normalized_at_zero,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.normalized_difference_norm_le,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.normalized_continuousAt_zero,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.outer_hasDerivAt_zero,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.reduced_derivative_real_positive,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.all_derivative_real_negative,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.reduced_difference_positive_for_small_positive_q,
      ``ManuscriptAudit.Paper8ContourAnalyticDifference.all_difference_negative_for_small_positive_q] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
