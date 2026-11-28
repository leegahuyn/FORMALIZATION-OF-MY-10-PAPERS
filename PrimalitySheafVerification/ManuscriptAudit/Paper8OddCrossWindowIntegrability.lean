import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossHeightWindowData

/-! The first-modulus height-cutoff coefficient is measurable and bounded on finite log-height windows. -/

namespace ManuscriptAudit.Paper8OddCrossWindowIntegrability

open MeasureTheory Set Paper8OddCrossHeightWindowData Paper8OddCrossLocalizedKernel
open Paper8OddCrossPoincareRowKernel
open scoped Topology

noncomputable section

def firstCrossCutoffCoefficient (q t : ℝ) : ℂ :=
  ∫ u : ℝ, crossHeightCutoffKernel q (Real.exp t) 2 u

private theorem continuous_cutoff_height : Continuous (fun p : ℝ × ℝ =>
    crossInvertedHeight (Real.exp p.1) 2 p.2) := by
  unfold crossInvertedHeight
  have hY : Continuous (fun p : ℝ × ℝ => Real.exp p.1) := Real.continuous_exp.comp continuous_fst
  exact hY.div (continuous_const.mul ((continuous_snd.pow 2).add (hY.pow 2))) (fun _ => by positivity)

theorem firstCrossCutoffCoefficient_measurable (q : ℝ) :
    Measurable (firstCrossCutoffCoefficient q) := by
  let F (p : ℝ × ℝ) := crossHeightCutoffKernel q (Real.exp p.1) 2 p.2
  have hS : MeasurableSet {p : ℝ × ℝ | q < crossInvertedHeight (Real.exp p.1) 2 p.2} :=
    (isOpen_lt continuous_const continuous_cutoff_height).measurableSet
  have hF : Measurable F :=
    (continuous_cross_phase_logHeight (by norm_num : (0 : ℝ) < 2)).measurable.piecewise hS measurable_const
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

private theorem crossCutoff_horizontal_support {q T t u : ℝ} (hq : 0 < q) (ht : t ≤ T)
    (hu : q < crossInvertedHeight (Real.exp t) 2 u) :
    |u| < Real.exp T / (4 * q) + 1 := by
  have hu' := (crossInvertedHeight_two_cutoff_iff hq (Real.exp_pos t) u).1 hu
  have hU : u ^ 2 < Real.exp T / (4 * q) :=
    hu'.trans_le ((sub_le_self _ (sq_nonneg _)).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ht) (by positivity)))
  have hs := sq_nonneg (|u| - 1 / 2)
  nlinarith [sq_abs u]

theorem firstCrossCutoffCoefficient_bounded_on_logHeight {q T : ℝ} (hq : 0 < q) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (-T) T, ‖firstCrossCutoffCoefficient q t‖ ≤ C := by
  let M := Real.exp T / (4 * q) + 1
  have hM : 0 < M := by unfold M; positivity
  let S : Set (ℝ × ℝ) := Icc (-T) T ×ˢ Icc (-M) M
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
    (continuous_cross_phase_logHeight (by norm_num : (0 : ℝ) < 2)).continuousOn
  have hC₀ : 0 ≤ C :=
    (norm_nonneg _).trans (hC (0, 0)
      ⟨⟨by linarith, hT⟩, ⟨by linarith, hM.le⟩⟩)
  refine ⟨C * (2 * M), by positivity, ?_⟩
  intro t ht
  let K := crossHeightCutoffKernel q (Real.exp t) 2
  let U := Ioo (-M) M
  have hInd : K = U.indicator K := by
    funext u
    by_cases hu : u ∈ U
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      apply if_neg
      intro hp
      exact hu (abs_lt.mp (crossCutoff_horizontal_support hq ht.2 hp))
  have hKBound (u : ℝ) (hu : u ∈ U) : ‖K u‖ ≤ C := by
    by_cases hp : q < crossInvertedHeight (Real.exp t) 2 u
    · change ‖crossHeightCutoffKernel q (Real.exp t) 2 u‖ ≤ C
      rw [crossHeightCutoffKernel, if_pos hp]
      exact hC (t, u) ⟨ht, Ioo_subset_Icc_self hu⟩
    · change ‖crossHeightCutoffKernel q (Real.exp t) 2 u‖ ≤ C
      rw [crossHeightCutoffKernel, if_neg hp, norm_zero]
      exact hC₀
  have hFin : volume U < ⊤ := by unfold U; rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hBound := norm_setIntegral_le_of_norm_le_const hFin hKBound
  have hVol : volume.real U = 2 * M := by
    unfold U
    rw [Real.volume_real_Ioo_of_le (by linarith : -M ≤ M)]
    ring
  rw [hVol] at hBound
  have hInt : (∫ u : ℝ, K u) = ∫ u in U, K u := by
    calc
      (∫ u : ℝ, K u) = ∫ u : ℝ, U.indicator K u := congrArg (fun f : ℝ → ℂ => ∫ u, f u) hInd
      _ = _ := integral_indicator measurableSet_Ioo
  change ‖∫ u : ℝ, K u‖ ≤ _
  rwa [hInt]

theorem weighted_firstCrossCutoffCoefficient_integrableOn {q T : ℝ} (hq : 0 < q) (hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) : ℂ) * firstCrossCutoffCoefficient q t) (Ioo (-T) T) := by
  obtain ⟨C, hC, hB⟩ := firstCrossCutoffCoefficient_bounded_on_logHeight hq hT
  let μ := (volume : Measure ℝ).restrict (Ioo (-T) T)
  have hg : Measurable (fun t : ℝ => (Real.exp (-t) : ℂ)) := by fun_prop
  have hm : AEStronglyMeasurable (fun t : ℝ => (Real.exp (-t) : ℂ) * firstCrossCutoffCoefficient q t) μ :=
    (hg.mul (firstCrossCutoffCoefficient_measurable q)).aestronglyMeasurable
  refine (integrable_const (μ := μ) (Real.exp T * C)).mono' hm ?_
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht
  have ht' : t ∈ Ioo (-T) T := ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [ht'.1]))
    (hB t (Ioo_subset_Icc_self ht')) (norm_nonneg _) (Real.exp_nonneg _)

end
end ManuscriptAudit.Paper8OddCrossWindowIntegrability

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossWindowIntegrability.firstCrossCutoffCoefficient_measurable,
      ``ManuscriptAudit.Paper8OddCrossWindowIntegrability.weighted_firstCrossCutoffCoefficient_integrableOn] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
