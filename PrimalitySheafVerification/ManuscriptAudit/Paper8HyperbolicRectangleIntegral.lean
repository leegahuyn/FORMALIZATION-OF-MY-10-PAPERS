import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassStripFubini

/-! A positive-height hyperbolic rectangle is bounded by its Euclidean integral with the inverse-square height factor. -/

namespace ManuscriptAudit.Paper8HyperbolicRectangleIntegral

open MeasureTheory Set UpperHalfPlane
open scoped ENNReal NNReal

noncomputable section

def upperRectangle (a b c d : ℝ) : Set ℍ :=
  {z | z.re ∈ Icc a b ∧ z.im ∈ Icc c d}

theorem measurable_upperRectangle (a b c d : ℝ) : MeasurableSet (upperRectangle a b c d) :=
  (measurableSet_Icc.preimage UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_Icc.preimage UpperHalfPlane.continuous_im.measurable)

private theorem preimage_upperRectangle {a b c d : ℝ} (hc : 0 < c) :
    Complex.measurableEquivRealProd.symm ⁻¹' (((↑) : ℍ → ℂ) '' upperRectangle a b c d) =
      Icc a b ×ˢ Icc c d := by
  ext p
  constructor
  · rintro ⟨z, hz, he⟩
    have hRe : z.re = p.1 := by
      simpa only [UpperHalfPlane.coe_re, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.re he
    have hIm : z.im = p.2 := by
      simpa only [UpperHalfPlane.coe_im, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.im he
    exact ⟨hRe ▸ hz.1, hIm ▸ hz.2⟩
  · intro hp
    have hPos : 0 < p.2 := hc.trans_le hp.2.1
    have hIm : (Complex.measurableEquivRealProd.symm p).im = p.2 := by
      simp only [Complex.measurableEquivRealProd_symm_apply]
    let z : ℍ := ⟨Complex.measurableEquivRealProd.symm p, hIm.symm ▸ hPos⟩
    have hRe : z.re = p.1 := by simp only [z, Complex.measurableEquivRealProd_symm_apply] <;> rfl
    have hzIm : z.im = p.2 := hIm
    exact ⟨z, ⟨hRe.symm ▸ hp.1, hzIm.symm ▸ hp.2⟩, rfl⟩

private def chartHeightWeight (z : ℍ) : ℝ≥0∞ :=
  ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)

private theorem measurable_chartHeightWeight : Measurable chartHeightWeight := by
  have hC : Continuous (fun z : ℍ => NNReal.mk z.im z.im_pos.le) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  unfold chartHeightWeight
  fun_prop

private theorem chartHeightWeight_eq (z : ℍ) :
    chartHeightWeight z = ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
  rw [chartHeightWeight, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, one_div, inv_pow]

theorem lintegral_upperRectangle_le_euclidean {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F)
    {a b c d B : ℝ} (hB : 0 < B) (hBc : B ≤ c) :
    (∫⁻ z in upperRectangle a b c d, F (z.re, z.im)) ≤
      ENNReal.ofReal ((B ^ 2)⁻¹) * ∫⁻ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, F p := by
  let R := upperRectangle a b c d
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let e := Complex.measurableEquivRealProd.symm
  let D (z : ℍ) := F (z.re, z.im)
  let G (w : ℂ) := F (w.re, w.im)
  let C := ENNReal.ofReal ((B ^ 2)⁻¹)
  have hR : MeasurableSet R := measurable_upperRectangle a b c d
  have hD : Measurable D :=
    hF.comp (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im).measurable
  have hP : MeasurePreserving UpperHalfPlane.coe μ
      ((volume : Measure ℂ).restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hPush := hP.setLIntegral_comp_emb measurableEmbedding_coe G R
  rw [Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    inter_eq_self_of_subset_left (image_subset_range _ _)] at hPush
  have hPull := Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage_emb
    e.measurableEmbedding G (((↑) : ℍ → ℂ) '' R)
  rw [show e ⁻¹' (((↑) : ℍ → ℂ) '' R) = Icc a b ×ˢ Icc c d from
      preimage_upperRectangle (hB.trans_le hBc)] at hPull
  have hFub : (∫⁻ z in R, D z ∂μ) = ∫⁻ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, F p := by
    calc
      _ = ∫⁻ w : ℂ in ((↑) : ℍ → ℂ) '' R, G w := hPush
      _ = ∫⁻ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, G (e p) := hPull.symm
      _ = _ := by
        apply lintegral_congr
        intro p
        simp [G, e, Complex.measurableEquivRealProd_symm_apply]
  change (∫⁻ z in R, D z) ≤ C * ∫⁻ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, F p
  rw [← hFub, ← lintegral_const_mul C hD, UpperHalfPlane.volume_def,
    setLIntegral_withDensity_eq_setLIntegral_mul μ measurable_chartHeightWeight hD hR]
  apply setLIntegral_mono' hR
  intro z hz
  change chartHeightWeight z * D z ≤ C * D z
  rw [chartHeightWeight_eq]
  apply mul_le_mul_right'
  apply ENNReal.ofReal_le_ofReal
  have hZ : B ≤ z.im := hBc.trans hz.2.1
  simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hB) (pow_le_pow_left₀ hB.le hZ 2)

end
end ManuscriptAudit.Paper8HyperbolicRectangleIntegral

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8HyperbolicRectangleIntegral.lintegral_upperRectangle_le_euclidean
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
