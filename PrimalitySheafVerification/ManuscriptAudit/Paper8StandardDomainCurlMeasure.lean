import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassTraceCurl
import PrimalitySheafVerification.ManuscriptAudit.Paper8StandardDomainSidePairing

/-! Exact Euclidean Fubini coordinates for the actual hyperbolic curl integral on the standard domain. -/

namespace ManuscriptAudit.Paper8StandardDomainCurlMeasure

open Filter Function MeasureTheory Set UpperHalfPlane MaassLaplacian
open Paper8MaassCurlCalculus Paper8MaassTraceCurl Paper8StandardDomainSidePairing
open scoped NNReal ENNReal Interval

noncomputable section

private def heightDensity (z : ℍ) : ℝ≥0 := ((1 / (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) ^ 2 : ℝ≥0)

private theorem heightDensity_measurable : Measurable heightDensity := by
  have hC : Continuous (fun z : ℍ => (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  unfold heightDensity
  fun_prop

theorem integral_weightedCurl_to_complex (J : ℂ → ℂ) {S : Set ℍ} (hS : MeasurableSet S) :
    (∫ z in S, weightedCurl J z) =
      ∫ w : ℂ in ((↑) : ℍ → ℂ) '' S, complexCurl J w := by
  let μ : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  have hμ : (volume : Measure ℍ) = μ.withDensity (fun z => (heightDensity z : ℝ≥0∞)) :=
    UpperHalfPlane.volume_def
  have hP : MeasurePreserving UpperHalfPlane.coe μ
      ((volume : Measure ℂ).restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hComp := (hP.restrict_image_emb measurableEmbedding_coe S).integral_comp
    measurableEmbedding_coe (complexCurl J)
  rw [Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    inter_eq_self_of_subset_left (image_subset_range _ _)] at hComp
  rw [hμ, setIntegral_withDensity_eq_setIntegral_smul heightDensity_measurable _ hS, ← hComp]
  refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
  simp only [heightDensity, weightedCurl, NNReal.smul_def, Complex.real_smul,
    NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk, Complex.ofReal_pow,
    Complex.ofReal_div, Complex.ofReal_one]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne'] <;> ring

private def region (Y : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-(1 / 2) : ℝ) (1 / 2) ∧ p.2 ∈ Icc (arcHeight p.1) Y}

private theorem arcHeight_continuous : Continuous arcHeight := by
  unfold arcHeight
  exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))

private theorem region_closed (Y : ℝ) : IsClosed (region Y) :=
  (isClosed_Icc.preimage continuous_fst).inter
    ((isClosed_le (arcHeight_continuous.comp continuous_fst) continuous_snd).inter
      (isClosed_le continuous_snd continuous_const))

private theorem region_compact (Y : ℝ) : IsCompact (region Y) :=
  ((isCompact_Icc (a := (-(1 / 2) : ℝ)) (b := 1 / 2)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := Y))).of_isClosed_subset (region_closed Y)
      (fun _ hp => ⟨hp.1, (Real.sqrt_nonneg _).trans hp.2.1, hp.2.2⟩)

private theorem coordinate_complex (p : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm p = complexPoint p.1 p.2 := by
  apply Complex.ext <;>
    simp [Complex.measurableEquivRealProd_symm_apply, complexPoint, Complex.mul_re, Complex.mul_im]

private theorem coordinate_region (Y : ℝ) :
    Complex.measurableEquivRealProd.symm ⁻¹'
      (((↑) : ℍ → ℂ) '' ModularGroup.truncatedFundamentalDomain Y) = region Y := by
  let e := Complex.measurableEquivRealProd.symm
  ext p
  have hSq : Complex.normSq (e p) = p.1 ^ 2 + p.2 ^ 2 := by
    rw [Complex.measurableEquivRealProd_symm_apply, Complex.normSq_apply]
    change p.1 * p.1 + p.2 * p.2 = _
    ring
  constructor
  · rintro ⟨z, hz, he⟩
    have hRe : z.re = p.1 := by
      simpa only [UpperHalfPlane.coe_re, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.re he
    have hIm : z.im = p.2 := by
      simpa only [UpperHalfPlane.coe_im, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.im he
    have hN : 1 ≤ p.1 ^ 2 + p.2 ^ 2 := by
      have h : 1 ≤ Complex.normSq (z : ℂ) := hz.1.1
      rw [he, hSq] at h
      exact h
    have hAbs : |p.1| ≤ 1 / 2 := hRe ▸ hz.1.2
    have hY : p.2 ≤ Y := hIm ▸ hz.2
    have hp : 0 ≤ p.2 := hIm ▸ z.im_pos.le
    exact ⟨abs_le.mp hAbs, (Real.sqrt_le_left hp).2 (by linarith), hY⟩
  · intro hp
    have hPos : 0 < p.2 := (arcHeight_pos (abs_le.mpr hp.1)).trans_le hp.2.1
    have hI : (e p).im = p.2 := by simp [e, Complex.measurableEquivRealProd_symm_apply]
    let z : ℍ := ⟨e p, hI.symm ▸ hPos⟩
    have hRe : z.re = p.1 := by simp [z, e, Complex.measurableEquivRealProd_symm_apply, UpperHalfPlane.re]
    have hNorm : 1 ≤ Complex.normSq (z : ℂ) := by
      change 1 ≤ Complex.normSq (e p)
      rw [hSq]
      have h := (Real.sqrt_le_left hPos.le).mp hp.2.1
      linarith
    exact ⟨z, ⟨⟨hNorm, hRe.symm ▸ abs_le.mpr hp.1⟩, hI.symm ▸ hp.2.2⟩, rfl⟩

theorem integral_truncated_weightedCurl (J : ℂ → ℂ) {Y : ℝ} (hY : 1 ≤ Y)
    (hC : ContinuousOn (complexCurl J) (((↑) : ℍ → ℂ) '' ModularGroup.truncatedFundamentalDomain Y)) :
    (∫ z in ModularGroup.truncatedFundamentalDomain Y, weightedCurl J z) =
      ∫ x in (-(1 / 2) : ℝ)..(1 / 2), ∫ y in arcHeight x..Y, complexCurl J (complexPoint x y) := by
  let S := ModularGroup.truncatedFundamentalDomain Y
  let e := Complex.measurableEquivRealProd.symm
  let R := region Y
  let f (p : ℝ × ℝ) := complexCurl J (e p)
  have hS : MeasurableSet S := (ModularGroup.isCompact_truncatedFundamentalDomain Y).measurableSet
  have hR : MeasurableSet R := (region_closed Y).measurableSet
  have hE : Continuous e := by
    change Continuous (fun p : ℝ × ℝ => e p)
    simp_rw [show ∀ p : ℝ × ℝ, e p = complexPoint p.1 p.2 from coordinate_complex]
    unfold complexPoint
    fun_prop
  have hMap : MapsTo e R (((↑) : ℍ → ℂ) '' S) := by
    rw [← coordinate_region Y]
    exact mapsTo_preimage _ _
  have hComp := (Complex.volume_preserving_equiv_real_prod.symm.restrict_preimage_emb
    e.measurableEmbedding (((↑) : ℍ → ℂ) '' S)).integral_comp e.measurableEmbedding (complexCurl J)
  rw [coordinate_region Y] at hComp
  rw [integral_weightedCurl_to_complex J hS, ← hComp]
  change (∫ p in R, f p) = _
  have hI : Integrable (R.indicator f) ((volume : Measure ℝ).prod volume) := by
    rw [integrable_indicator_iff hR, ← Measure.volume_eq_prod]
    exact (hC.comp hE.continuousOn hMap).integrableOn_compact (region_compact Y)
  rw [← integral_indicator hR, Measure.volume_eq_prod, integral_prod _ hI]
  let X := Icc (-(1 / 2) : ℝ) (1 / 2)
  have hX : MeasurableSet X := measurableSet_Icc
  have hIcc :
      (∫ x : ℝ, ∫ y : ℝ, R.indicator f (x, y)) =
        ∫ x : ℝ in X, ∫ y : ℝ in Icc (arcHeight x) Y, f (x, y) := by
    rw [← integral_indicator hX]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ X
    · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      have hx' : x ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := hx
      change (region Y).indicator f (x, y) = (Icc (arcHeight x) Y).indicator (fun y => f (x, y)) y
      by_cases hy : y ∈ Icc (arcHeight x) Y
      · rw [indicator_of_mem (show (x, y) ∈ region Y from ⟨hx', hy⟩), indicator_of_mem hy]
      · rw [indicator_of_notMem (fun h : (x, y) ∈ region Y => hy h.2), indicator_of_notMem hy]
    · rw [indicator_of_notMem hx]
      calc
        _ = ∫ _ : ℝ, (0 : ℂ) := by
          apply integral_congr_ae
          apply Eventually.of_forall
          intro y
          exact indicator_of_notMem (fun h => hx h.1) _
        _ = _ := integral_zero
  rw [hIcc, intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2),
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun hX (fun x hx => ?_)
  have hL : arcHeight x ≤ Y := (Real.sqrt_le_one.2 (by nlinarith [sq_nonneg x])).trans hY
  rw [intervalIntegral.integral_of_le hL, ← integral_Icc_eq_integral_Ioc]
  simp only [f, e, coordinate_complex]

end
end ManuscriptAudit.Paper8StandardDomainCurlMeasure

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8StandardDomainCurlMeasure.integral_truncated_weightedCurl
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
