import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ComplexCorrection
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorOrdinaryDictionary
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianComplexDictionary
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplexComparison

/-! The corrected p. 335 ordinary exterior identity on the full punctured complex disk. -/

namespace ManuscriptAudit.Paper8ExteriorOrdinaryComplexDictionary

open Set
open Paper8InsideComplexAnalytic (standard)
open Paper8ExteriorComplex (exterior standard_inv_eq_exterior radius_power_le)
open Paper8ExteriorComplexHolomorphy (exterior_differentiableOn_unit_disk normalizedCover)
open Paper8ExteriorPrincipal (principalRoot principalNormalization principal_normalization_eq_literal)
open Paper8ExteriorComplexComparison (standard_ofReal_inverse)
open Paper8EulerianComplexPentagonal (complexSeries complexSeries_ofReal complexSeries_differentiableOn)
open Paper8EulerianComplexDictionary (literalPsi literalPsi_eq_complexSeries)
open Paper8EulerianDictionary (unilateralTheta_eq_pentagonalSeries)
open Paper8ComplexCorrection (correction correction_ofReal correction_differentiableOn)
open Paper8ExteriorOrdinaryDictionary (p335_unweighted_exterior_corrected)

noncomputable section

private theorem positive_axis_eq {r : ℝ} (hr : 0 < r) (h₁ : r < 1) :
    exterior (r : ℂ) = 2 * complexSeries (r : ℂ) - correction (r : ℂ) := by
  have hr₀ : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hNorm : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using h₁
  rw [← standard_inv_eq_exterior hr₀ hNorm, standard_ofReal_inverse hr h₁,
    complexSeries_ofReal hr.le h₁, ← unilateralTheta_eq_pentagonalSeries hr h₁,
    correction_ofReal hr h₁]
  exact_mod_cast p335_unweighted_exterior_corrected hr h₁

theorem exterior_eq_two_complexSeries_sub_correction {q : ℂ} (hq : ‖q‖ < 1) :
    exterior q = 2 * complexSeries q - correction q := by
  let disk := Metric.ball (0 : ℂ) 1
  have hF : AnalyticOnNhd ℂ exterior disk :=
    exterior_differentiableOn_unit_disk.analyticOnNhd Metric.isOpen_ball
  have hConst : DifferentiableOn ℂ (fun _ : ℂ => (2 : ℂ)) disk := differentiableOn_const (2 : ℂ)
  have hG : AnalyticOnNhd ℂ (fun z => (2 : ℂ) * complexSeries z - correction z) disk :=
    ((hConst.mul complexSeries_differentiableOn).sub correction_differentiableOn)
      .analyticOnNhd Metric.isOpen_ball
  have hC : IsPreconnected disk := (convex_ball (0 : ℂ) 1).isPreconnected
  have h0 : (0 : ℂ) ∈ disk := by simp [disk]
  have hAccum :
      (0 : ℂ) ∈ closure ({z | exterior z = (2 : ℂ) * complexSeries z - correction z} \ {0}) := by
    refine Metric.mem_closure_iff.mpr ?_
    intro ε hε
    let r : ℝ := min (ε / 2) (1 / 2)
    have hr : 0 < r := lt_min (div_pos hε (by norm_num)) (by norm_num)
    have hεr : r < ε := (min_le_left _ _).trans_lt (by linarith only [hε])
    have hr₁ : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
    refine ⟨(r : ℂ), ⟨positive_axis_eq hr hr₁, ?_⟩, ?_⟩
    · have hn : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      simpa using hn
    · simpa only [dist_zero_left, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg hr.le] using hεr
  have hmem : q ∈ disk := by simpa only [disk, Metric.mem_ball, dist_zero_right] using hq
  exact hF.eqOn_of_preconnected_of_mem_closure hG hC h0 hAccum hmem

theorem p335_unweighted_exterior_corrected_complex {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    standard q⁻¹ = 2 * literalPsi q - correction q := by
  rw [standard_inv_eq_exterior hq₀ hq, literalPsi_eq_complexSeries hq]
  exact exterior_eq_two_complexSeries_sub_correction hq

theorem literal_normalized_corrected_on_slit {q : ℂ}
    (hSlit : q ∈ Complex.slitPlane) (hq : ‖q‖ < 1) :
    (q⁻¹) ^ (-((24 : ℂ)⁻¹)) * standard q⁻¹ =
      principalRoot q * (2 * literalPsi q - correction q) := by
  rw [← principal_normalization_eq_literal hSlit hq, principalNormalization,
    literalPsi_eq_complexSeries hq, exterior_eq_two_complexSeries_sub_correction hq]

theorem normalizedCover_corrected {w : ℂ} (hw : ‖w‖ < 1) :
    normalizedCover w = w * (2 * literalPsi (w ^ (24 : ℕ)) - correction (w ^ (24 : ℕ))) := by
  have hNorm : ‖w ^ (24 : ℕ)‖ < 1 := by
    rw [norm_pow]
    exact (radius_power_le (norm_nonneg w) hw.le 23).trans_lt hw
  rw [normalizedCover, literalPsi_eq_complexSeries hNorm,
    exterior_eq_two_complexSeries_sub_correction hNorm]

end
end ManuscriptAudit.Paper8ExteriorOrdinaryComplexDictionary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorOrdinaryComplexDictionary.exterior_eq_two_complexSeries_sub_correction,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryComplexDictionary.p335_unweighted_exterior_corrected_complex,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryComplexDictionary.literal_normalized_corrected_on_slit,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryComplexDictionary.normalizedCover_corrected] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
