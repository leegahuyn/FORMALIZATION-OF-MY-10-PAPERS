import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossHeightWindowData
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossLocalizedFourier

/-! The localized nonzero cross Fourier coefficient persists on an open interval of heights. -/

namespace ManuscriptAudit.Paper8OddCrossHeightWindow

open Set MeasureTheory
open Paper8OddCrossHeightWindowData Paper8OddCrossLocalizedKernel Paper8OddCrossLocalizedFourier
open Paper8OddCrossLocalizedRows Paper8OddCrossFirstCoefficient Paper8OddCrossPoincareUnfold
open Paper8OddCrossPoincareRowKernel Paper8OddCrossPoincareConvergence Paper8OddCrossCuspCutoff
open scoped Topology

noncomputable section

theorem exists_cross_cutoff_logHeight_window :
    ∃ q ε : ℝ, ∃ z : ℂ, 1 / 16 < q ∧ q < 1 / 4 ∧ 0 < ε ∧ z ≠ 0 ∧
      ∀ t : ℝ, |t| < ε →
        (∀ (D : ℕ), 2 ≤ D → ∀ u : ℝ,
          crossHeightCutoffKernel q (Real.exp t) (2 * (D : ℝ)) u = 0) ∧
        0 < (z * ∫ u : ℝ, crossHeightCutoffKernel q (Real.exp t) 2 u).re := by
  let z := (crossRealKernel 0 1 2 0)⁻¹
  have hz : z ≠ 0 := inv_ne_zero crossFirstPhase_ne_zero
  let P (p : ℝ × ℝ) := z * crossRealKernel 0 (Real.exp p.1) 2 p.2
  have hPC : Continuous P := continuous_const.mul (continuous_cross_phase_logHeight (by norm_num))
  have hP₀ : P (0, 0) = 1 := by
    change z * crossRealKernel 0 (Real.exp 0) 2 0 = 1
    rw [Real.exp_zero]
    exact inv_mul_cancel₀ crossFirstPhase_ne_zero
  let U : Set (ℝ × ℝ) := {p | (1 / 2 : ℝ) < (P p).re}
  have hU : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp hPC)
  have hU₀ : (0, 0) ∈ U := by
    change (1 / 2 : ℝ) < (P (0, 0)).re
    rw [hP₀, Complex.one_re] <;> norm_num
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hU₀)
  let d := min (δ / 2) 1
  have hd : 0 < d := lt_min (by positivity) zero_lt_one
  have hdδ : d < δ := (min_le_left _ _).trans_lt (by linarith)
  have hd1 : d ≤ 1 := min_le_right _ _
  let q := 1 / (4 * (1 + d ^ 2))
  have hDsq : d ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hd.le hd1 2
  have hqLo : (1 / 16 : ℝ) < q := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hqHi : q < (1 / 4 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) (by nlinarith [sq_pos_of_pos hd])
  have hq : 0 < q := (by norm_num : 0 < (1 / 16 : ℝ)).trans hqLo
  let X (t : ℝ) := Real.exp t / (4 * q) - (Real.exp t) ^ 2
  let Y (t : ℝ) := 1 / (16 * Real.exp t)
  have hXC : Continuous X := (Real.continuous_exp.div_const _).sub (Real.continuous_exp.pow 2)
  have hYC : Continuous Y :=
    continuous_const.div (continuous_const.mul Real.continuous_exp) (fun _ => by positivity)
  have hX₀ : X 0 = d ^ 2 := by
    unfold X q
    rw [Real.exp_zero, one_pow]
    have hD : (1 + d ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp [hD] <;> ring
  have hY₀ : Y 0 = 1 / 16 := by unfold Y; rw [Real.exp_zero, mul_one]
  let V : Set ℝ := {t | 0 < X t} ∩ {t | X t < δ ^ 2} ∩ {t | Y t < q}
  have hV : IsOpen V := ((isOpen_lt continuous_const hXC).inter
    (isOpen_lt hXC continuous_const)).inter (isOpen_lt hYC continuous_const)
  have hV₀ : (0 : ℝ) ∈ V := by
    change (0 < X 0 ∧ X 0 < δ ^ 2) ∧ Y 0 < q
    rw [hX₀, hY₀]
    exact ⟨⟨sq_pos_of_pos hd, pow_lt_pow_left₀ hdδ hd.le (by decide : 2 ≠ 0)⟩, hqLo⟩
  obtain ⟨η, hη, hVB⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hV₀)
  let ε := min δ η
  refine ⟨q, ε, z, hqLo, hqHi, lt_min hδ hη, hz, ?_⟩
  intro t ht
  have htδ : |t| < δ := ht.trans_le (min_le_left _ _)
  have htη : |t| < η := ht.trans_le (min_le_right _ _)
  have hVt : t ∈ V := hVB (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using htη)
  change (0 < X t ∧ X t < δ ^ 2) ∧ Y t < q at hVt
  obtain ⟨⟨hXt, hXδ⟩, hYt⟩ := hVt
  have hy : 0 < Real.exp t := Real.exp_pos t
  constructor
  · intro D hD u
    exact if_neg (not_lt_of_ge ((crossInvertedHeight_large_modulus_le hy hD u).trans hYt.le))
  let r := Real.sqrt (X t)
  have hr : 0 < r := Real.sqrt_pos.2 hXt
  have hrδ : r < δ := by
    have h : r ^ 2 < δ ^ 2 := by dsimp only [r]; rwa [Real.sq_sqrt hXt.le]
    simpa only [abs_of_pos hr, abs_of_pos hδ] using sq_lt_sq.mp h
  have hSupport (u : ℝ) :
      q < crossInvertedHeight (Real.exp t) 2 u ↔ u ∈ Ioo (-r) r :=
    crossInvertedHeight_two_cutoff_interval hq hy hXt u
  let K := crossRealKernel 0 (Real.exp t) 2
  have hKC : Continuous K := crossRealKernel_continuous 0 hy (by norm_num)
  have hLo (u : ℝ) (hu : u ∈ Ioo (-r) r) : (1 / 2 : ℝ) ≤ (z * K u).re := by
    have huδ : |u| < δ := (abs_lt.mpr hu).trans hrδ
    have hp : (t, u) ∈ Metric.ball (0, 0) δ := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt (by simpa only [Real.dist_eq, sub_zero] using htδ)
        (by simpa only [Real.dist_eq, sub_zero] using huδ)
    exact (show (1 / 2 : ℝ) < (z * K u).re from hBall hp).le
  have hInd : crossHeightCutoffKernel q (Real.exp t) 2 = (Ioo (-r) r).indicator K := by
    funext u
    change (if q < crossInvertedHeight (Real.exp t) 2 u then K u else 0) = _
    by_cases hu : u ∈ Ioo (-r) r
    · exact (if_pos ((hSupport u).2 hu)).trans (Set.indicator_of_mem hu K).symm
    · exact (if_neg (fun h => hu ((hSupport u).1 h))).trans (Set.indicator_of_notMem hu K).symm
  rw [hInd, integral_indicator measurableSet_Ioo]
  exact rotated_interval_integral_positive K hKC z hr hLo

theorem exists_positive_odd_cross_fourier_on_logHeight_window :
    ∃ q ε : ℝ, ∃ z : ℂ, 1 / 16 < q ∧ q < 1 / 4 ∧ 0 < ε ∧ z ≠ 0 ∧
      ∀ t : ℝ, |t| < ε →
        0 < (z * ∫ x in (0 : ℝ)..(1 : ℝ), ∑' i : CrossIndex,
          oddCrossHeightCutoffFourierTerm q (pointAtHeight x (Real.exp_pos t)) i).re := by
  obtain ⟨q, ε, z, hqLo, hqHi, hε, hz, hW⟩ := exists_cross_cutoff_logHeight_window
  refine ⟨q, ε, z, hqLo, hqHi, hε, hz, ?_⟩
  intro t ht
  obtain ⟨hKill, hFirst⟩ := hW t ht
  have hq : 0 < q := (by norm_num : 0 < (1 / 16 : ℝ)).trans hqLo
  rw [odd_cross_height_cutoff_fourier_expansion hq (Real.exp_pos t)]
  have hSupport (D : ℕ) (hD : D ∉ ({0} : Finset ℕ)) :
      crossSum (Nat.succ_pos D) *
        ∫ u : ℝ, crossHeightCutoffKernel q (Real.exp t) (2 * ((D + 1 : ℕ) : ℝ)) u = 0 := by
    have hD0 : D ≠ 0 := by simpa only [Finset.mem_singleton] using hD
    simp only [hKill (D + 1) (by omega), integral_zero, mul_zero]
  rw [tsum_eq_sum hSupport, Finset.sum_singleton]
  simpa only [zero_add, Nat.cast_one, mul_one, crossSum_one, one_mul] using hFirst

end
end ManuscriptAudit.Paper8OddCrossHeightWindow

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossHeightWindow.exists_positive_odd_cross_fourier_on_logHeight_window
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
