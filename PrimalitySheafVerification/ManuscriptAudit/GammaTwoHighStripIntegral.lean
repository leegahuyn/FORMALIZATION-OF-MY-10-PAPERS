import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Prod
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoHighStripMeasure

/-! Exact hyperbolic integral of a height density in the measurable width-two chart. -/

namespace ManuscriptAudit.GammaTwoHighStripIntegral

open MeasureTheory Set GammaTwoHighStripMeasure
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoCurvilinearTileStokes
open scoped UpperHalfPlane NNReal

noncomputable section

private def rectangle : Set (ℝ × ℝ) := Ico (0 : ℝ) 2 ×ˢ Ioi (1 : ℝ)

private theorem strip_image :
    Complex.measurableEquivRealProd '' (UpperHalfPlane.coe '' strip) = rectangle := by
  ext p
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨hz.2, hz.1⟩
  · rintro ⟨hx, hy⟩
    let z : ℍ := ⟨⟨p.1, p.2⟩, zero_lt_one.trans hy⟩
    exact ⟨(z : ℂ), ⟨z, ⟨hy, hx⟩, rfl⟩, by cases p; rfl⟩

private theorem real_density_cancel (f : ℝ → ℝ) (z : ℍ) :
    hyperbolicDensityNNReal z • (z.im ^ 2 * f z.im) = f z.im := by
  have hc : (hyperbolicDensityNNReal z : ℝ) * z.im ^ 2 = 1 := by
    simp only [hyperbolicDensityNNReal, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk]
    field_simp [z.im_ne_zero]
  rw [NNReal.smul_def, smul_eq_mul, ← mul_assoc, hc, one_mul]

private theorem euclidean_upper_image (f : ℝ → ℝ) :
    (∫ z in strip, f z.im ∂((volume : Measure ℂ).comap UpperHalfPlane.coe)) =
      ∫ w in UpperHalfPlane.coe '' strip, f w.im ∂(volume : Measure ℂ) := by
  have hp : MeasurePreserving UpperHalfPlane.coe
      ((volume : Measure ℂ).comap UpperHalfPlane.coe)
      ((volume : Measure ℂ).restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, UpperHalfPlane.measurableEmbedding_coe.map_comap⟩
  have he := (hp.setIntegral_image_emb UpperHalfPlane.measurableEmbedding_coe
    (fun w : ℂ => f w.im) strip).symm
  rw [Measure.restrict_restrict_of_subset (image_subset_range _ _)] at he
  exact he

private theorem rectangle_integral (f : ℝ → ℝ) :
    (∫ p in rectangle, f p.2 ∂(volume : Measure (ℝ × ℝ))) =
      2 * ∫ y in Ioi (1 : ℝ), f y ∂(volume : Measure ℝ) := by
  change (∫ p, f p.2 ∂(((volume : Measure ℝ).prod volume).restrict
      (Ico (0 : ℝ) 2 ×ˢ Ioi (1 : ℝ)))) = _
  rw [← Measure.prod_restrict, integral_fun_snd, smul_eq_mul]
  have hM : ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 2)).real univ = 2 := by
    rw [Measure.real_def, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ico]
    norm_num
  rw [hM]

theorem height_integral (f : ℝ → ℝ) :
    (∫ z in strip, z.im ^ 2 * f z.im ∂hyperbolicMeasure) =
      2 * ∫ y in Ioi (1 : ℝ), f y ∂(volume : Measure ℝ) := by
  calc
    _ = ∫ z in strip, f z.im ∂((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
      rw [hyperbolicMeasure_eq_withDensityNNReal,
        setIntegral_withDensity_eq_setIntegral_smul
          hyperbolicDensityNNReal_continuous.measurable _ strip_measurable]
      exact setIntegral_congr_fun strip_measurable (fun z _ => real_density_cancel f z)
    _ = ∫ w in UpperHalfPlane.coe '' strip, f w.im ∂(volume : Measure ℂ) :=
      euclidean_upper_image f
    _ = ∫ p in rectangle, f p.2 ∂(volume : Measure (ℝ × ℝ)) := by
      rw [← strip_image]
      exact (Complex.volume_preserving_equiv_real_prod.setIntegral_image_emb
        Complex.measurableEquivRealProd.measurableEmbedding (fun p => f p.2)
        (UpperHalfPlane.coe '' strip)).symm
    _ = _ := rectangle_integral f

end
end ManuscriptAudit.GammaTwoHighStripIntegral

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GammaTwoHighStripIntegral.height_integral
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
