import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareUnfold

/-! A height cutoff isolates the first cross modulus and gives a nonzero exact geometric integral. -/

namespace ManuscriptAudit.Paper8OddCrossLocalizedKernel

open Filter MeasureTheory Set
open Paper8OddCrossPoincareUnfold Paper8OddCrossPoincareRowKernel
open Paper8OddCrossPoincareKernel Paper8OddCrossPoincareHeight Paper8OddCrossCuspNormalization
open Paper8OddCrossCuspPhase MaassLaplacian
open scoped Topology

noncomputable section

def crossInvertedHeight (y c u : ℝ) : ℝ := y / (c ^ 2 * (u ^ 2 + y ^ 2))

def crossHeightCutoffKernel (q y c u : ℝ) : ℂ :=
  if q < crossInvertedHeight y c u then crossRealKernel 0 y c u else 0

theorem crossInvertedHeight_one_large_modulus_le {D : ℕ} (hD : 2 ≤ D) (u : ℝ) :
    crossInvertedHeight 1 (2 * (D : ℝ)) u ≤ 1 / 16 := by
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hA : (16 : ℝ) ≤ (2 * (D : ℝ)) ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ)) hD' 2
    nlinarith
  have hB : (1 : ℝ) ≤ u ^ 2 + 1 := by nlinarith [sq_nonneg u]
  have hDen : (16 : ℝ) ≤ (2 * (D : ℝ)) ^ 2 * (u ^ 2 + 1) := by
    have h := mul_le_mul hA hB (by norm_num : 0 ≤ (1 : ℝ)) (sq_nonneg (2 * (D : ℝ)))
    simpa only [mul_one] using h
  unfold crossInvertedHeight
  rw [one_pow]
  exact one_div_le_one_div_of_le (by norm_num) hDen

theorem crossFirstPhase_ne_zero : crossRealKernel 0 1 2 0 ≠ 0 := by
  have hW : complexPoint 0 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num [complexPoint_im] at hi
  have hR : normalizedNegativeRoot (complexPoint 0 1) ≠ 0 := by
    intro h
    have hn := normalizedNegativeRoot_norm hW
    simp [h] at hn
  unfold crossRealKernel
  simp only [Complex.cpow_zero, mul_one]
  exact mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hR) (Complex.exp_ne_zero _)

private theorem first_height_support {d : ℝ} (hd : 0 < d) (u : ℝ) :
    (1 / (4 * (1 + d ^ 2)) : ℝ) < crossInvertedHeight 1 2 u ↔ u ∈ Ioo (-d) d := by
  unfold crossInvertedHeight
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num, one_pow,
    one_div_lt_one_div (by positivity) (by positivity)]
  have h : 4 * (u ^ 2 + 1) < 4 * (1 + d ^ 2) ↔ u ^ 2 < d ^ 2 := by
    constructor <;> intro h <;> linarith
  rw [h, sq_lt_sq, abs_of_pos hd, abs_lt] <;> rfl

theorem rotated_interval_integral_positive (K : ℝ → ℂ) (hK : Continuous K) (z : ℂ)
    {d : ℝ} (hd : 0 < d) (hLo : ∀ u ∈ Ioo (-d) d, (1 / 2 : ℝ) ≤ (z * K u).re) :
    0 < (z * ∫ u in Ioo (-d) d, K u).re := by
  let S := Ioo (-d) d
  let P (u : ℝ) := z * K u
  have hP : Continuous P := continuous_const.mul hK
  have hPI : IntegrableOn P S :=
    (hP.continuousOn.integrableOn_Icc (μ := (volume : Measure ℝ))).mono_set Ioo_subset_Icc_self
  have hPR : IntegrableOn (fun u => (P u).re) S :=
    (Complex.continuous_re.comp hP).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hIntegralLo : (∫ _ : ℝ in S, (1 / 2 : ℝ)) ≤ ∫ u in S, (P u).re := by
    apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => by norm_num)) hPR
    filter_upwards [ae_restrict_mem (show MeasurableSet S from measurableSet_Ioo)] with u hu
    exact hLo u hu
  have hPos : 0 < ∫ u in S, (P u).re := by
    apply lt_of_lt_of_le ?_ hIntegralLo
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith : -d ≤ d), smul_eq_mul]
    exact mul_pos (by linarith) (by norm_num)
  have hRe := integral_re hPI
  change (∫ u in S, (P u).re) = (∫ u in S, z * K u).re at hRe
  rw [integral_const_mul] at hRe
  rw [← hRe]
  exact hPos

theorem exists_crossHeightCutoff_first_modulus_nonzero :
    ∃ q : ℝ, 1 / 16 < q ∧ q < 1 / 4 ∧
      (∀ (D : ℕ), 2 ≤ D → ∀ u : ℝ, crossHeightCutoffKernel q 1 (2 * (D : ℝ)) u = 0) ∧
      (∫ u : ℝ, crossHeightCutoffKernel q 1 2 u) ≠ 0 := by
  let K := crossRealKernel 0 1 2
  let P (u : ℝ) := (K 0)⁻¹ * K u
  have hK : Continuous K := crossRealKernel_continuous 0 (by norm_num) (by norm_num)
  have hP : Continuous P := continuous_const.mul hK
  have hP₀ : P 0 = 1 := inv_mul_cancel₀ crossFirstPhase_ne_zero
  have hOpen : IsOpen {u : ℝ | (1 / 2 : ℝ) < (P u).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hP)
  have hMem : (0 : ℝ) ∈ {u : ℝ | (1 / 2 : ℝ) < (P u).re} := by
    change (1 / 2 : ℝ) < (P 0).re
    rw [hP₀, Complex.one_re] <;> norm_num
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.1 (hOpen.mem_nhds hMem)
  let d := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  have hdδ : d ≤ δ := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  let q := 1 / (4 * (1 + d ^ 2))
  have hSq : d ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hd.le hd1 2
  have hqLo : (1 / 16 : ℝ) < q :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hqHi : q < (1 / 4 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) (by nlinarith [sq_pos_of_pos hd])
  refine ⟨q, hqLo, hqHi, ?_, ?_⟩
  · intro D hD u
    exact if_neg (not_lt_of_ge ((crossInvertedHeight_one_large_modulus_le hD u).trans hqLo.le))
  let S := Ioo (-d) d
  have hInd : crossHeightCutoffKernel q 1 2 = S.indicator K := by
    funext u
    unfold crossHeightCutoffKernel
    change (if (1 / (4 * (1 + d ^ 2)) : ℝ) < crossInvertedHeight 1 2 u then K u else 0) = _
    by_cases hu : u ∈ S
    · exact (if_pos ((first_height_support hd u).mpr hu)).trans (Set.indicator_of_mem hu K).symm
    · exact (if_neg (fun h => hu ((first_height_support hd u).mp h))).trans
        (Set.indicator_of_notMem hu K).symm
  have hLo (u : ℝ) (hu : u ∈ S) : (1 / 2 : ℝ) ≤ (P u).re := by
    have ha : |u| < d := abs_lt.mpr hu
    have hb : u ∈ Metric.ball 0 δ := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ha.trans_le hdδ
    exact (show (1 / 2 : ℝ) < (P u).re from hBall hb).le
  have hRot := rotated_interval_integral_positive K hK ((K 0)⁻¹) hd hLo
  rw [hInd, integral_indicator (show MeasurableSet S from measurableSet_Ioo)]
  intro hZero
  rw [hZero, mul_zero, Complex.zero_re] at hRot
  exact (lt_irrefl _) hRot

end
end ManuscriptAudit.Paper8OddCrossLocalizedKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossLocalizedKernel.exists_crossHeightCutoff_first_modulus_nonzero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
