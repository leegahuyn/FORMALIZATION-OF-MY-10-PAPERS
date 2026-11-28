import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassStripFubini

/-! The hyperbolic integral of a nonnegative continuous density on a high strip in horizontal coordinates. -/

namespace ManuscriptAudit.Paper8HighStripFubini

open Filter MeasureTheory Set UpperHalfPlane MaassLaplacian
open scoped ENNReal NNReal

noncomputable section

def upperStripPoint (x y : ℝ) : ℍ :=
  ⟨complexPoint x (max y 1), by rw [complexPoint_im]; exact zero_lt_one.trans_le (le_max_right _ _)⟩

theorem continuous_upperStripPoint : Continuous (fun p : ℝ × ℝ => upperStripPoint p.1 p.2) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun p : ℝ × ℝ => complexPoint p.1 (max p.2 1))
  unfold complexPoint
  fun_prop

def highHorizontalStrip (a b T : ℝ) : Set ℍ :=
  {z | z.re ∈ Icc a b ∧ T ≤ z.im}

theorem measurable_highHorizontalStrip (a b T : ℝ) : MeasurableSet (highHorizontalStrip a b T) :=
  (measurableSet_Icc.preimage UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_Ici.preimage UpperHalfPlane.continuous_im.measurable)

def weightedHorizontalSlice (D : ℍ → ℝ) (a b y : ℝ) : ℝ :=
  (∫ x in a..b, D (upperStripPoint x y)) / y ^ 2

private def absHeightDensity (z : ℂ) : ℝ≥0∞ := ↑((1 / ‖z.im‖₊ : ℝ≥0) ^ 2)

private theorem hyperbolic_strip_to_complex {D : ℍ → ℝ≥0∞} (hD : Measurable D) (a b T : ℝ) :
    (∫⁻ z in highHorizontalStrip a b T, D z) =
      ∫⁻ q : ℂ in ((↑) : ℍ → ℂ) '' highHorizontalStrip a b T, absHeightDensity q * D (ofComplex q) := by
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let f (q : ℂ) := absHeightDensity q * D (ofComplex q)
  let S := highHorizontalStrip a b T
  have hS : MeasurableSet S := measurable_highHorizontalStrip a b T
  have hMeasure : MeasurePreserving UpperHalfPlane.coe μ
      ((volume : Measure ℂ).restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hPush := hMeasure.setLIntegral_comp_emb measurableEmbedding_coe f S
  rw [Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    inter_eq_self_of_subset_left (image_subset_range _ _)] at hPush
  have hDensity : Measurable
      (fun z : ℍ => (↑((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞)) := by
    have hC : Continuous (fun z : ℍ => NNReal.mk z.im z.im_pos.le) :=
      UpperHalfPlane.continuous_im.subtype_mk _
    fun_prop
  rw [UpperHalfPlane.volume_def, setLIntegral_withDensity_eq_setLIntegral_mul μ hDensity hD hS, ← hPush]
  refine setLIntegral_congr_fun hS (fun z _ => ?_)
  change (↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) : ℝ≥0∞) * D z =
      absHeightDensity (z : ℂ) * D (ofComplex (z : ℂ))
  have hZ : ofComplex (z : ℂ) = z := by rw [ofComplex_apply_of_im_pos z.im_pos]
  have hNorm : ‖(z : ℂ).im‖₊ = NNReal.mk z.im z.im_pos.le :=
    Real.nnnorm_of_nonneg z.im_pos.le
  rw [hZ, absHeightDensity, hNorm]

private theorem preimage_highHorizontalStrip (a b T : ℝ) (hT : 1 ≤ T) :
    Complex.measurableEquivRealProd.symm ⁻¹' (((↑) : ℍ → ℂ) '' highHorizontalStrip a b T) =
      Icc a b ×ˢ Ici T := by
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
    have hPos : 0 < p.2 := zero_lt_one.trans_le (hT.trans hp.2)
    have hIm : (Complex.measurableEquivRealProd.symm p).im = p.2 := by
      simp only [Complex.measurableEquivRealProd_symm_apply]
    let z : ℍ := ⟨Complex.measurableEquivRealProd.symm p, hIm.symm ▸ hPos⟩
    have hRe : z.re = p.1 := by simp only [z, Complex.measurableEquivRealProd_symm_apply] <;> rfl
    have hzIm : z.im = p.2 := hIm
    exact ⟨z, ⟨hRe.symm ▸ hp.1, hzIm.symm ▸ hp.2⟩, rfl⟩

private theorem coordinate_complex (p : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm p = complexPoint p.1 p.2 := by
  apply Complex.ext <;>
    simp [Complex.measurableEquivRealProd_symm_apply, complexPoint, Complex.mul_re, Complex.mul_im]

private theorem ofComplex_coordinate_eq {p : ℝ × ℝ} (h : 1 ≤ p.2) :
    ofComplex (Complex.measurableEquivRealProd.symm p) = upperStripPoint p.1 p.2 := by
  rw [coordinate_complex, ofComplex_apply_of_im_pos
    (by rw [complexPoint_im]; exact zero_lt_one.trans_le h)]
  apply UpperHalfPlane.ext
  change complexPoint p.1 p.2 = complexPoint p.1 (max p.2 1)
  rw [max_eq_left h]

theorem lintegral_hyperbolic_highStrip {D : ℍ → ℝ} (hD : Continuous D) (hD₀ : ∀ z, 0 ≤ D z)
    {a b T : ℝ} (hab : a ≤ b) (hT : 1 ≤ T) :
    (∫⁻ z in highHorizontalStrip a b T, ENNReal.ofReal (D z)) =
      ∫⁻ y in Ici T, ENNReal.ofReal (weightedHorizontalSlice D a b y) := by
  let e := Complex.measurableEquivRealProd.symm
  let f (q : ℂ) := absHeightDensity q * ENNReal.ofReal (D (ofComplex q))
  let K (p : ℝ × ℝ) : ℝ := D (upperStripPoint p.1 p.2) / p.2 ^ 2
  have hK : Measurable K :=
    (hD.measurable.comp continuous_upperStripPoint.measurable).div (measurable_snd.pow_const 2)
  have hSet : MeasurableSet (Icc a b ×ˢ Ici T) := measurableSet_Icc.prod measurableSet_Ici
  have hPull :=
    Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage_emb
      e.measurableEmbedding f (((↑) : ℍ → ℂ) '' highHorizontalStrip a b T)
  rw [preimage_highHorizontalStrip a b T hT] at hPull
  have hEq : (∫⁻ p in Icc a b ×ˢ Ici T, ENNReal.ofReal (K p)) =
      ∫⁻ p in Icc a b ×ˢ Ici T, f (e p) := by
    refine setLIntegral_congr_fun hSet (fun p hp => ?_)
    have hPos : 0 < p.2 := zero_lt_one.trans_le (hT.trans hp.2)
    have hW : absHeightDensity (e p) = ENNReal.ofReal ((p.2 ^ 2)⁻¹) := by
      rw [absHeightDensity, ← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp [e, Complex.measurableEquivRealProd_symm_apply, Real.norm_eq_abs, abs_of_pos hPos, inv_pow]
    dsimp only [K, f]
    rw [hW, ofComplex_coordinate_eq (hT.trans hp.2), div_eq_inv_mul,
      ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _))]
  rw [hyperbolic_strip_to_complex (ENNReal.measurable_ofReal.comp hD.measurable), ← hPull, ← hEq,
    Measure.volume_eq_prod, setLIntegral_prod_symm _ (ENNReal.measurable_ofReal.comp hK).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ici (fun y _ => ?_)
  have hCy : Continuous (fun x : ℝ => K (x, y)) :=
    (hD.comp (continuous_upperStripPoint.comp (continuous_id.prodMk continuous_const))).div_const _
  have hIy : IntegrableOn (fun x : ℝ => K (x, y)) (Icc a b) :=
    hCy.continuousOn.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hIy
    (Eventually.of_forall (fun x => div_nonneg (hD₀ _) (sq_nonneg _)))]
  simp only [K, weightedHorizontalSlice, integral_div, intervalIntegral.integral_of_le hab,
    integral_Icc_eq_integral_Ioc]

end
end ManuscriptAudit.Paper8HighStripFubini

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8HighStripFubini.lintegral_hyperbolic_highStrip
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
