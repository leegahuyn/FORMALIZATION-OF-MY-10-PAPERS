import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Prod
import PrimalitySheafVerification.ManuscriptAudit.Paper8ModularCoreRectangle
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPeterssonMass
import PrimalitySheafVerification.ManuscriptAudit.Paper8HighStripFubini

/-! Quantitative transport of invariant densities from the standard domain to its bounded rectangular extension. -/

namespace ManuscriptAudit.Paper8ModularCoreIntegral

open MeasureTheory Set UpperHalfPlane MaassLaplacian
open Paper8ModularCoreRectangle Paper8EtaPeterssonMass (translate)
open scoped ENNReal NNReal MatrixGroups

noncomputable section

theorem measurable_modularCoreRectangle (T : ℝ) : MeasurableSet (modularCoreRectangle T) :=
  (measurableSet_le UpperHalfPlane.continuous_re.measurable.abs measurable_const).inter
    ((measurableSet_le measurable_const UpperHalfPlane.continuous_im.measurable).inter
      (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const))

theorem lintegral_modularCoreRectangle_le_two {D : ℍ → ℝ≥0∞}
    (hD : ∀ (g : SL(2, ℤ)) (z : ℍ), D (g • z) = D z) (T : ℝ) :
    (∫⁻ z in modularCoreRectangle T, D z) ≤ 2 * ∫⁻ z in ModularGroup.fd, D z := by
  let g := ModularGroup.S⁻¹
  let S := translate g ModularGroup.fd
  have hSub : modularCoreRectangle T ⊆ ModularGroup.fd ∪ S := by
    intro z hz
    rcases modularCoreRectangle_cover T hz with h | h
    · exact Or.inl h.1
    · exact Or.inr ⟨ModularGroup.S • z, h.1, inv_smul_smul ModularGroup.S z⟩
  have hP : MeasurePreserving (fun z : ℍ => g • z) (volume : Measure ℍ) volume :=
    measurePreserving_smul (g : GL (Fin 2) ℝ) volume
  have hEmb : MeasurableEmbedding (fun z : ℍ => g • z) :=
    measurableEmbedding_const_smul (g : GL (Fin 2) ℝ)
  have hS : (∫⁻ z in S, D z) = ∫⁻ z in ModularGroup.fd, D z := by
    simpa only [hD g] using (hP.setLIntegral_comp_emb hEmb D ModularGroup.fd).symm
  calc
    _ ≤ ∫⁻ z in ModularGroup.fd ∪ S, D z := lintegral_mono_set hSub
    _ ≤ (∫⁻ z in ModularGroup.fd, D z) + (∫⁻ z in S, D z) := lintegral_union_le _ _ _
    _ = _ := by rw [hS, two_mul]

def euclideanCoreRectangle (T : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(1 / 2)) (1 / 2) ×ˢ Icc coreMinimumHeight T

def coreCoordinatePoint (p : ℝ × ℝ) : ℍ :=
  ⟨complexPoint p.1 (max p.2 coreMinimumHeight), by
    rw [complexPoint_im]
    exact coreMinimumHeight_pos.trans_le (le_max_right _ _)⟩

theorem continuous_coreCoordinatePoint : Continuous coreCoordinatePoint := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun p : ℝ × ℝ => complexPoint p.1 (max p.2 coreMinimumHeight))
  unfold complexPoint
  fun_prop

private theorem preimage_euclideanCoreRectangle (T : ℝ) :
    Complex.measurableEquivRealProd.symm ⁻¹' (((↑) : ℍ → ℂ) '' modularCoreRectangle T) =
      euclideanCoreRectangle T := by
  ext p
  constructor
  · rintro ⟨z, hz, he⟩
    have hRe : z.re = p.1 := by
      simpa only [UpperHalfPlane.coe_re, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.re he
    have hIm : z.im = p.2 := by
      simpa only [UpperHalfPlane.coe_im, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.im he
    exact ⟨abs_le.mp (hRe ▸ hz.1), hIm ▸ hz.2.1, hIm ▸ hz.2.2⟩
  · intro hp
    have hPos : 0 < p.2 := coreMinimumHeight_pos.trans_le hp.2.1
    have hIm : (Complex.measurableEquivRealProd.symm p).im = p.2 := by
      simp only [Complex.measurableEquivRealProd_symm_apply]
    let z : ℍ := ⟨Complex.measurableEquivRealProd.symm p, hIm.symm ▸ hPos⟩
    have hRe : z.re = p.1 := by simp only [z, Complex.measurableEquivRealProd_symm_apply] <;> rfl
    have hzIm : z.im = p.2 := hIm
    exact ⟨z, ⟨hRe.symm ▸ abs_le.mpr hp.1, hzIm.symm ▸ hp.2.1, hzIm.symm ▸ hp.2.2⟩, rfl⟩

private theorem coreCoordinate_eq {p : ℝ × ℝ} (hp : coreMinimumHeight ≤ p.2) :
    ofComplex (Complex.measurableEquivRealProd.symm p) = coreCoordinatePoint p := by
  have hCoord : Complex.measurableEquivRealProd.symm p = complexPoint p.1 p.2 := by
    apply Complex.ext <;>
      simp [Complex.measurableEquivRealProd_symm_apply, complexPoint, Complex.mul_re, Complex.mul_im]
  rw [hCoord, ofComplex_apply_of_im_pos (by rw [complexPoint_im]; exact coreMinimumHeight_pos.trans_le hp)]
  apply UpperHalfPlane.ext
  change complexPoint p.1 p.2 = complexPoint p.1 (max p.2 coreMinimumHeight)
  rw [max_eq_left hp]

private def heightWeight (z : ℍ) : ℝ≥0∞ :=
  ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)

private theorem heightWeight_measurable : Measurable heightWeight := by
  have hC : Continuous (fun z : ℍ => NNReal.mk z.im z.im_pos.le) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  unfold heightWeight
  fun_prop

private theorem heightWeight_mul (z : ℍ) : heightWeight z * ENNReal.ofReal (z.im ^ 2) = 1 := by
  have hW : heightWeight z = ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
    rw [heightWeight, ← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, one_div, inv_pow]
  rw [hW, ← ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _)),
    inv_mul_cancel₀ (pow_ne_zero 2 z.im_ne_zero), ENNReal.ofReal_one]

theorem lintegral_euclideanCore_le_hyperbolic {D : ℍ → ℝ≥0∞} (hD : Measurable D) (T : ℝ) :
    (∫⁻ p in euclideanCoreRectangle T, D (coreCoordinatePoint p)) ≤
      ENNReal.ofReal (T ^ 2) * ∫⁻ z in modularCoreRectangle T, D z := by
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let R := modularCoreRectangle T
  let e := Complex.measurableEquivRealProd.symm
  have hR : MeasurableSet R := measurable_modularCoreRectangle T
  have hSet : MeasurableSet (euclideanCoreRectangle T) := measurableSet_Icc.prod measurableSet_Icc
  have hP : MeasurePreserving UpperHalfPlane.coe μ
      ((volume : Measure ℂ).restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hPush := hP.setLIntegral_comp_emb measurableEmbedding_coe (fun w => D (ofComplex w)) R
  rw [Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    inter_eq_self_of_subset_left (image_subset_range _ _)] at hPush
  have hComp : (∫⁻ z in R, D z ∂μ) = ∫⁻ w : ℂ in ((↑) : ℍ → ℂ) '' R, D (ofComplex w) := by
    rw [← hPush]
    apply setLIntegral_congr_fun hR
    intro z _
    rw [ofComplex_apply_of_im_pos z.im_pos]
  have hPull := Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage_emb
    e.measurableEmbedding (fun w => D (ofComplex w)) (((↑) : ℍ → ℂ) '' R)
  rw [show e ⁻¹' (((↑) : ℍ → ℂ) '' R) = euclideanCoreRectangle T from
      preimage_euclideanCoreRectangle T] at hPull
  have hEucl :
      (∫⁻ p in euclideanCoreRectangle T, D (coreCoordinatePoint p)) = ∫⁻ z in R, D z ∂μ := by
    rw [hComp, ← hPull]
    apply setLIntegral_congr_fun hSet
    intro p hp
    rw [show ofComplex (e p) = coreCoordinatePoint p from coreCoordinate_eq hp.2.1]
  have hWeight : (∫⁻ z in R, D z ∂μ) =
      ∫⁻ z in R, ENNReal.ofReal (z.im ^ 2) * D z := by
    have hG : Measurable (fun z : ℍ => ENNReal.ofReal (z.im ^ 2) * D z) :=
      (ENNReal.measurable_ofReal.comp (UpperHalfPlane.continuous_im.pow 2).measurable).mul hD
    rw [UpperHalfPlane.volume_def, setLIntegral_withDensity_eq_setLIntegral_mul μ heightWeight_measurable hG hR]
    apply setLIntegral_congr_fun hR
    intro z _
    change D z = heightWeight z * (ENNReal.ofReal (z.im ^ 2) * D z)
    rw [← mul_assoc, heightWeight_mul, one_mul]
  rw [hEucl, hWeight, ← lintegral_const_mul _ hD]
  apply setLIntegral_mono' hR
  intro z hz
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ z.im_pos.le hz.2.2 2)) _

end
end ManuscriptAudit.Paper8ModularCoreIntegral

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ModularCoreIntegral.lintegral_modularCoreRectangle_le_two,
      ``ManuscriptAudit.Paper8ModularCoreIntegral.lintegral_euclideanCore_le_hyperbolic] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
