import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoQuotientHeightIntegral

/-! Compact height profiles give integrable densities for every actual quotient measure. -/

namespace ManuscriptAudit.GammaTwoProfileIntegrability

open Set MeasureTheory GammaTwoHighStripMeasure GammaTwoQuotientHeightIntegral
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoCurvilinearTileStokes
open scoped UpperHalfPlane NNReal

noncomputable section

private theorem euclidean_integrable (f : ℝ → ℝ) (hf : Continuous f) {b : ℝ}
    (hz : ∀ y > b, f y = 0) :
    IntegrableOn (fun z : ℍ => f z.im) strip ((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
  let A := UpperHalfPlane.coe '' strip
  let B := Metric.closedBall (0 : ℂ) (2 + b)
  let F : ℂ → ℝ := fun w => f w.im
  have hA : MeasurableSet A := UpperHalfPlane.measurableEmbedding_coe.measurableSet_image' strip_measurable
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hCompact : IntegrableOn F B (volume : Measure ℂ) :=
    (hf.comp Complex.continuous_im).continuousOn.integrableOn_compact isCompact_closedBall
  have hAB : IntegrableOn F (A ∩ B) (volume : Measure ℂ) := hCompact.mono_set inter_subset_right
  have he : A.indicator F = (A ∩ B).indicator F := by
    funext w
    by_cases hw : w ∈ A
    · rw [indicator_of_mem hw]
      by_cases hb : w ∈ B
      · rw [indicator_of_mem (show w ∈ A ∩ B from ⟨hw, hb⟩)]
      · rw [indicator_of_notMem (fun h : w ∈ A ∩ B => hb h.2)]
        obtain ⟨z, hzStrip, rfl⟩ := hw
        apply hz
        by_contra! hUpper
        apply hb
        rw [Metric.mem_closedBall, dist_zero_right]
        change z.im ≤ b at hUpper
        have hR : 0 ≤ z.re := hzStrip.2.1
        have hY : 0 ≤ z.im := z.im_pos.le
        exact (Complex.norm_le_abs_re_add_abs_im (z : ℂ)).trans (by
          change |z.re| + |z.im| ≤ 2 + b
          rw [abs_of_nonneg hR, abs_of_nonneg hY]
          exact add_le_add hzStrip.2.2.le hUpper)
    · rw [indicator_of_notMem hw, indicator_of_notMem (fun h : w ∈ A ∩ B => hw h.1)]
  have hI : IntegrableOn F A (volume : Measure ℂ) := by
    rw [← integrable_indicator_iff hA, he, integrable_indicator_iff (hA.inter hB)]
    exact hAB
  have hMap := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (image_subset_range UpperHalfPlane.coe strip)).mp hI
  have hPre : UpperHalfPlane.coe ⁻¹' A = strip := by
    exact preimage_image_eq _ UpperHalfPlane.measurableEmbedding_coe.injective
  rw [hPre] at hMap
  exact hMap

private theorem hyperbolic_density_cancel (f : ℝ → ℝ) (z : ℍ) :
    hyperbolicDensityNNReal z • (z.im ^ 2 * f z.im) = f z.im := by
  have hc : (hyperbolicDensityNNReal z : ℝ) * z.im ^ 2 = 1 := by
    simp only [hyperbolicDensityNNReal, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk]
    field_simp [z.im_ne_zero]
  rw [NNReal.smul_def, smul_eq_mul, ← mul_assoc, hc, one_mul]

theorem integrable_strip_profile (f : ℝ → ℝ) (hf : Continuous f) {b : ℝ}
    (hz : ∀ y > b, f y = 0) :
    IntegrableOn (fun z : ℍ => z.im ^ 2 * f z.im) strip hyperbolicMeasure := by
  rw [IntegrableOn, hyperbolicMeasure_eq_withDensityNNReal, restrict_withDensity strip_measurable,
    integrable_withDensity_iff_integrable_smul hyperbolicDensityNNReal_continuous.measurable]
  simp_rw [hyperbolic_density_cancel]
  exact euclidean_integrable f hf hz

theorem integrable_quotient_profile (D : GammaTwoFundamentalDomain) (f : ℝ → ℝ) (hf : Continuous f)
    (hLow : ∀ y ≤ 1, f y = 0) {b : ℝ} (hHigh : ∀ y > b, f y = 0) :
    Integrable (fun q => quotientHeight q ^ 2 * f (quotientHeight q)) D.quotientMeasure := by
  let A := gammaTwoQuotientMk '' strip
  let F : GammaTwoQuotient → ℝ := fun q => quotientHeight q ^ 2 * f (quotientHeight q)
  have hA : MeasurableSet A := GammaTwoFundamentalDomain.quotientImage_measurable strip_measurable
  have hF : Measurable F := (quotientHeight_measurable.pow_const 2).mul
    (hf.measurable.comp quotientHeight_measurable)
  have hR : IntegrableOn F A D.quotientMeasure := by
    change Integrable F (D.quotientMeasure.restrict A)
    rw [← quotient_strip_measure D]
    have hmk : Measurable gammaTwoQuotientMk := measurable_quotient_mk''
    apply (integrable_map_measure hF.aestronglyMeasurable hmk.aemeasurable).mpr
    apply (integrable_strip_profile f hf hHigh).congr
    exact (ae_restrict_iff' strip_measurable).mpr (Filter.Eventually.of_forall (fun z hz => by
      change z.im ^ 2 * f z.im = F (gammaTwoQuotientMk z)
      unfold F
      rw [quotientHeight_high z (show 1 < z.im from hz.1).le]))
  apply ((integrable_indicator_iff hA).mpr hR).congr
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q ∈ A
  · rw [indicator_of_mem hq]
  · rw [indicator_of_notMem hq]
    have h : quotientHeight q ≤ 1 := le_of_not_gt (fun h => hq (mem_strip_image_of_height h))
    simp only [F, hLow _ h, mul_zero]

end
end ManuscriptAudit.GammaTwoProfileIntegrability

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GammaTwoProfileIntegrability.integrable_strip_profile,
      ``ManuscriptAudit.GammaTwoProfileIntegrability.integrable_quotient_profile] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
