import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Measure.WithDensity
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassStripCover
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-! Global invariant Maass mass implies the actual coordinate cusp energy condition. -/

namespace ManuscriptAudit.Paper8MaassStripFubini

open Set Function MeasureTheory UpperHalfPlane
open MaassLaplacian Paper8MaassStripCover
open Paper8EtaCosetMass (cosetCells)
open scoped MatrixGroups ENNReal

noncomputable section

def normSquareDensity (F : ℂ → ℂ) (z : ℍ) : ℝ≥0∞ := ENNReal.ofReal (‖F z‖ ^ 2)

def stripEnergy (F : ℂ → ℂ) (g : SL(2, ℤ)) (width y : ℝ) : ℝ :=
  (∫ x : ℝ in (0 : ℝ)..width, ‖F (g • ofComplex (complexPoint x y) : ℍ)‖ ^ 2) / y ^ 2

private def heightDensity (z : ℂ) : ℝ≥0∞ := ↑((1 / ‖z.im‖₊ : ℝ≥0) ^ 2)

private theorem measurable_highStrip (w : ℝ) : MeasurableSet (highStrip w) :=
  (measurableSet_le measurable_const UpperHalfPlane.continuous_re.measurable).inter
    ((measurableSet_le UpperHalfPlane.continuous_re.measurable measurable_const).inter
      (measurableSet_le measurable_const UpperHalfPlane.continuous_im.measurable))

private theorem hyperbolic_integral_to_complex {D : ℍ → ℝ≥0∞} (hD : Measurable D) (w : ℝ) :
    (∫⁻ z in highStrip w, D z) =
      ∫⁻ q : ℂ in ((↑) : ℍ → ℂ) '' highStrip w, heightDensity q * D (ofComplex q) := by
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  let f (q : ℂ) := heightDensity q * D (ofComplex q)
  let S := highStrip w
  have hS : MeasurableSet S := measurable_highStrip w
  have hMeasure : MeasurePreserving UpperHalfPlane.coe μ
      ((volume : Measure ℂ).restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hPush := hMeasure.setLIntegral_comp_emb measurableEmbedding_coe f S
  rw [Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    inter_eq_self_of_subset_left (image_subset_range _ _)] at hPush
  have hDensity : Measurable
      (fun z : ℍ => (↑((1 / (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) ^ 2) : ℝ≥0∞)) := by
    have hC : Continuous (fun z : ℍ => (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) :=
      UpperHalfPlane.continuous_im.subtype_mk _
    fun_prop
  rw [UpperHalfPlane.volume_def, setLIntegral_withDensity_eq_setLIntegral_mul μ hDensity hD hS, ← hPush]
  refine setLIntegral_congr_fun hS (fun z _ => ?_)
  simp [f, heightDensity, Real.nnnorm_of_nonneg z.im_pos.le]

private def stripCoordinates (w : ℝ) : Set (ℝ × ℝ) := Icc 0 w ×ˢ Ici 1

private theorem coordinates_preimage (w : ℝ) :
    Complex.measurableEquivRealProd.symm ⁻¹' (((↑) : ℍ → ℂ) '' highStrip w) =
      stripCoordinates w := by
  ext p
  constructor
  · rintro ⟨z, hz, he⟩
    have hRe : z.re = p.1 := by
      simpa only [UpperHalfPlane.coe_re, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.re he
    have hIm : z.im = p.2 := by
      simpa only [UpperHalfPlane.coe_im, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.im he
    exact ⟨⟨hRe ▸ hz.1, hRe ▸ hz.2.1⟩, hIm ▸ hz.2.2⟩
  · intro hp
    have hPos : 0 < p.2 := zero_lt_one.trans_le hp.2
    have hIm : (Complex.measurableEquivRealProd.symm p).im = p.2 := by
      simp only [Complex.measurableEquivRealProd_symm_apply]
    let z : ℍ := ⟨Complex.measurableEquivRealProd.symm p, hIm.symm ▸ hPos⟩
    have hRe : z.re = p.1 := by simp only [z, Complex.measurableEquivRealProd_symm_apply] <;> rfl
    have hzIm : z.im = p.2 := hIm
    exact ⟨z, ⟨hRe.symm ▸ hp.1.1, hRe.symm ▸ hp.1.2, hzIm.symm ▸ hp.2⟩, rfl⟩

private def coordinateUpper (p : ℝ × ℝ) : ℍ :=
  ⟨complexPoint p.1 (max p.2 1), by rw [complexPoint_im]; exact zero_lt_one.trans_le (le_max_right _ _)⟩

private theorem continuous_coordinateUpper : Continuous coordinateUpper := by
  refine Continuous.subtype_mk ?_ _
  unfold complexPoint
  fun_prop

private theorem coord_upper_eq_ofComplex {p : ℝ × ℝ} (hp : 1 ≤ p.2) :
    coordinateUpper p = ofComplex (complexPoint p.1 p.2) := by
  have hPos : 0 < (complexPoint p.1 p.2).im := by rw [complexPoint_im]; exact zero_lt_one.trans_le hp
  rw [ofComplex_apply_of_im_pos hPos]
  apply UpperHalfPlane.ext
  change complexPoint p.1 (max p.2 1) = complexPoint p.1 p.2
  rw [max_eq_left hp]

private theorem coordinate_complex_eq (p : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm p = complexPoint p.1 p.2 := by
  apply Complex.ext <;>
    simp [Complex.measurableEquivRealProd_symm_apply, complexPoint, Complex.mul_re, Complex.mul_im]

theorem stripEnergy_integrable_of_global_mass {H : Subgroup SL(2, ℤ)} {F : ℂ → ℂ}
    (hF : Measurable (fun z : ℍ => F z))
    (hInv : ∀ h : SL(2, ℤ), h ∈ H → ∀ z : ℍ, ‖F (h • z : ℍ)‖ = ‖F z‖)
    (hMass : (∫⁻ z in cosetCells H ModularGroup.fd, normSquareDensity F z) < ⊤)
    (g : SL(2, ℤ)) (w : ℕ) :
    IntegrableOn (stripEnergy F g (w : ℝ)) (Ioi 1) := by
  let D (z : ℍ) := normSquareDensity F (g • z)
  have hD : Measurable D := by
    have hS : Measurable (fun z : ℍ => g • z) := measurable_const_smul (g : GL (Fin 2) ℝ)
    unfold D normSquareDensity
    exact ENNReal.measurable_ofReal.comp ((hF.comp hS).norm.pow_const 2)
  have hHigh : (∫⁻ z in highStrip (w : ℝ), D z) < ⊤ :=
    cusp_mass_lt_top H (normSquareDensity F) (fun h hh z => by simp [normSquareDensity, hInv h hh z])
      hMass g w
  let K (p : ℝ × ℝ) := ‖F (g • coordinateUpper p : ℍ)‖ ^ 2 / p.2 ^ 2
  have hK : Measurable K := by
    have hS : Measurable (fun z : ℍ => g • z) := measurable_const_smul (g : GL (Fin 2) ℝ)
    unfold K
    exact ((hF.comp (hS.comp continuous_coordinateUpper.measurable)).norm.pow_const 2).div
      (measurable_snd.pow_const 2)
  let μ := (volume : Measure ℝ).restrict (Icc 0 (w : ℝ))
  let ν := (volume : Measure ℝ).restrict (Ici 1)
  have hSet : MeasurableSet (stripCoordinates (w : ℝ)) := measurableSet_Icc.prod measurableSet_Ici
  have hFin : (∫⁻ p in stripCoordinates (w : ℝ), ENNReal.ofReal (K p)) < ⊤ := by
    rw [hyperbolic_integral_to_complex hD] at hHigh
    let e := Complex.measurableEquivRealProd.symm
    let f (q : ℂ) := heightDensity q * D (ofComplex q)
    have hPull :=
      Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage_emb
        e.measurableEmbedding f (((↑) : ℍ → ℂ) '' highStrip (w : ℝ))
    rw [coordinates_preimage] at hPull
    have heq : (∫⁻ p in stripCoordinates (w : ℝ), ENNReal.ofReal (K p)) =
        ∫⁻ p in stripCoordinates (w : ℝ), f (e p) := by
      refine setLIntegral_congr_fun hSet (fun p hp => ?_)
      have hPos : 0 < p.2 := zero_lt_one.trans_le hp.2
      have hW : heightDensity (e p) = ENNReal.ofReal ((p.2 ^ 2)⁻¹) := by
        rw [heightDensity, ← ENNReal.ofReal_coe_nnreal]
        congr 1
        simp [e, Complex.measurableEquivRealProd_symm_apply, Real.norm_eq_abs, abs_of_pos hPos, inv_pow]
      dsimp only [K, f, D, normSquareDensity]
      have hUpper : ofComplex (e p) = coordinateUpper p := by
        rw [show e p = complexPoint p.1 p.2 from coordinate_complex_eq p,
          coord_upper_eq_ofComplex hp.2]
      rw [hW, hUpper, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr (sq_nonneg _))]
    exact (heq.trans hPull).trans_lt hHigh
  have hFinite : (∫⁻ p, ENNReal.ofReal (K p) ∂μ.prod ν) < ⊤ := by
    simpa only [μ, ν, Measure.prod_restrict, stripCoordinates] using hFin
  have hInt : Integrable K (μ.prod ν) := by
    refine ⟨hK.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal ?_).mpr hFinite⟩
    exact Eventually.of_forall (fun p => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hInner := hInt.integral_prod_right
  change IntegrableOn (fun y : ℝ => ∫ x : ℝ in Icc 0 (w : ℝ), K (x, y)) (Ici 1) at hInner
  have hEq (y : ℝ) (hy : y ∈ Ici (1 : ℝ)) :
      (∫ x : ℝ in Icc 0 (w : ℝ), K (x, y)) = stripEnergy F g (w : ℝ) y := by
    have hPoint (x : ℝ) :
        K (x, y) = ‖F (g • ofComplex (complexPoint x y) : ℍ)‖ ^ 2 / y ^ 2 := by
      simp only [K, coord_upper_eq_ofComplex (p := (x, y)) hy]
    simp only [hPoint, integral_div, stripEnergy, intervalIntegral.integral_of_le (Nat.cast_nonneg w),
      integral_Icc_eq_integral_Ioc]
  exact (hInner.congr_fun hEq measurableSet_Ici).mono_set Ioi_subset_Ici_self


end
end ManuscriptAudit.Paper8MaassStripFubini

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassStripFubini.stripEnergy_integrable_of_global_mass
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
