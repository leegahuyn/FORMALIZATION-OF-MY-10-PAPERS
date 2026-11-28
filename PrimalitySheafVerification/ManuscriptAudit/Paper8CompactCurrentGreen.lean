import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8StandardGreenRegularity
import PrimalitySheafVerification.ManuscriptAudit.Paper8ModularHeightCutoff

/-! Green's formula for smooth automorphic currents supported below an invariant cusp height. -/

namespace ManuscriptAudit.Paper8CompactCurrentGreen

open Filter Function Set MeasureTheory UpperHalfPlane ModularForm
open FiniteIndexWeightZeroCosets Paper8EtaCosetMass Paper8EtaPeterssonMass
open Paper8ActualEtaSquaredModularity Paper8MaassWirtinger Paper8MaassCurlCalculus
open Paper8MaassTraceCurl Paper8WeightTwoCosetTrace Paper8StandardDomainCurrentGreen
open Paper8GlobalWeightTwoGreen Paper8StandardGreenRegularity Paper8ModularHeightCutoff
open scoped MatrixGroups ModularForm Topology

noncomputable section

private theorem isOpen_upper : IsOpen {w : ℂ | 0 < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

theorem slashComplex_contDiffAt (J : ℂ → ℂ) (g : SL(2, ℤ)) (z : ℍ) {n : ℕ∞ω}
    (hJ : ContDiffAt ℝ n J (g • z : ℍ)) : ContDiffAt ℝ n (slashComplex J g) z := by
  have hDen : ContDiffAt ℝ n (denominator g) z := by unfold denominator; fun_prop
  have hNum : ContDiffAt ℝ n (fun w : ℂ => (g 0 0 : ℂ) * w + (g 0 1 : ℂ)) z := by
    fun_prop
  have hFrac : ContDiffAt ℝ n (fractionalLinear g) z := by
    unfold fractionalLinear
    simp only [div_eq_mul_inv]
    change ContDiffAt ℝ n
      ((fun w : ℂ => (g 0 0 : ℂ) * w + (g 0 1 : ℂ)) * (denominator g)⁻¹) z
    exact hNum.mul (hDen.inv (denominator_ne_zero g z))
  have hJ' : ContDiffAt ℝ n J (fractionalLinear g z) := by rw [fractionalLinear_eq]; exact hJ
  have hPow : ContDiffAt ℝ n (fun w : ℂ => denominator g w ^ 2) z := by
    change ContDiffAt ℝ n (denominator g ^ (2 : ℕ)) z
    exact hDen.pow 2
  change ContDiffAt ℝ n ((J ∘ fractionalLinear g) * (denominator g ^ (2 : ℕ))⁻¹) z
  exact (hJ'.comp _ hFrac).mul (hPow.inv (pow_ne_zero 2 (denominator_ne_zero g z)))

theorem trace_contDiffOn (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (J : ℂ → ℂ) {n : ℕ∞ω}
    (hJ : ContDiffOn ℝ n J {w : ℂ | 0 < w.im})
    (hInv : ∀ h : SL(2, ℤ), h ∈ H →
      (fun z : ℍ => J z) ∣[(2 : ℤ)] h = fun z : ℍ => J z) :
    ContDiffOn ℝ n (asComplexCurrent (trace H (fun z : ℍ => J z) hInv)) {w : ℂ | 0 < w.im} := by
  letI := rightCosetFintype H
  intro w hw
  let z : ℍ := ⟨w, hw⟩
  let A (q : RightCoset H) := slashComplex J (cellRepresentative H q)
  have hSum : ContDiffAt ℝ n (fun v : ℂ => ∑ q : RightCoset H, A q v) w := by
    apply ContDiffAt.sum
    intro q _
    let u : ℍ := cellRepresentative H q • z
    exact slashComplex_contDiffAt J (cellRepresentative H q) z
      ((hJ u u.im_pos).contDiffAt (isOpen_upper.mem_nhds u.im_pos))
  apply (hSum.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [isOpen_upper.mem_nhds hw] with v hv
  let u : ℍ := ⟨v, hv⟩
  change trace H (fun z : ℍ => J z) hInv (ofComplex v) = ∑ q : RightCoset H, A q v
  rw [ofComplex_apply_of_im_pos hv]
  unfold trace
  apply Finset.sum_congr rfl
  intro q _
  change cosetSlash H (fun z : ℍ => J z) hInv q u = slashComplex J (cellRepresentative H q) u
  conv_lhs => rw [← cellRepresentative_mk H q, cosetSlash_mk]
  rw [slashComplex_coe]

theorem weightedCurl_continuous {J : ℂ → ℂ} (hJ : ContDiffOn ℝ 1 J {w : ℂ | 0 < w.im}) :
    Continuous (weightedCurl J) := by
  let S : Set ℂ := {w : ℂ | 0 < w.im}
  have hD (v : ℂ) : ContinuousOn (fun w : ℂ => fderiv ℝ J w v) S := by
    let L (w : ℂ) := (w, v)
    have hL : Continuous L := continuous_id.prodMk continuous_const
    have hm : MapsTo L S (S ×ˢ (univ : Set ℂ)) := fun _ hw => ⟨hw, mem_univ _⟩
    have hc := (hJ.continuousOn_fderivWithin_apply isOpen_upper.uniqueDiffOn (le_refl 1)).comp
      hL.continuousOn hm
    refine hc.congr ?_
    intro w hw
    change fderiv ℝ J w v = fderivWithin ℝ J S w v
    rw [fderivWithin_of_isOpen isOpen_upper hw]
  have hC : ContinuousOn (complexCurl J) S := by
    unfold complexCurl
    exact (continuousOn_const.mul (hD 1)).sub (hD Complex.I)
  have hPull : Continuous (fun z : ℍ => complexCurl J z) :=
    hC.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)
  have hHeight : Continuous (fun z : ℍ => ((z.im ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.pow 2)
  exact hHeight.mul hPull

theorem weightedCurl_eq_zero_above {J : ℂ → ℂ} {B : ℝ}
    (hSupport : ∀ z : ℍ, B < maximumHeight z → J z = 0)
    (z : ℍ) (hz : B < maximumHeight z) : weightedCurl J z = 0 := by
  let g := Classical.choose (ModularGroup.exists_max_im z)
  have hg : B < (g • z).im := hz
  have hComplex : B < (fractionalLinear g z).im := by
    rw [fractionalLinear_eq, UpperHalfPlane.coe_im]
    exact hg
  have hAction : ContinuousAt (fun w : ℂ => (fractionalLinear g w).im) z :=
    Complex.continuous_im.continuousAt.comp ((fractionalLinear_hasDerivAt g z).continuousAt)
  have hLocal : J =ᶠ[𝓝 (z : ℂ)] (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [isOpen_upper.mem_nhds z.im_pos,
      hAction.tendsto.eventually (Ioi_mem_nhds hComplex)]
      with w hw hW
    let u : ℍ := ⟨w, hw⟩
    apply hSupport u
    have hV : B < (g • u).im := by
      change B < (fractionalLinear g u).im at hW
      rw [fractionalLinear_eq, UpperHalfPlane.coe_im] at hW
      exact hW
    exact hV.trans_le (im_smul_le_maximumHeight u g)
  unfold weightedCurl complexCurl
  rw [hLocal.fderiv_eq (𝕜 := ℝ), fderiv_const]
  simp

theorem integrableOn_cusp_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (f : ℍ → E) {B : ℝ}
    (hF : Continuous f) (hSupport : ∀ z : ℍ, B < maximumHeight z → f z = 0) :
    IntegrableOn f (cosetCells H ModularGroup.fd) := by
  letI := rightCosetFintype H
  let T := cosetCells H (ModularGroup.truncatedFundamentalDomain B)
  have hT : IsCompact T := by
    apply isCompact_iUnion
    intro q
    exact (ModularGroup.isCompact_truncatedFundamentalDomain B).image
      (continuous_const_smul (cellRepresentative H q : GL (Fin 2) ℝ))
  have hI : Integrable (T.indicator f) := by
    rw [integrable_indicator_iff hT.measurableSet]
    exact hF.continuousOn.integrableOn_compact hT
  refine hI.integrableOn.congr_fun ?_ ?_
  · intro z hz
    by_cases hzT : z ∈ T
    · exact indicator_of_mem hzT _
    · rw [indicator_of_notMem hzT]
      symm
      apply hSupport
      apply lt_of_not_ge
      intro hMax
      obtain ⟨q, u, hu, rfl⟩ := mem_iUnion.mp hz
      rw [maximumHeight_invariant] at hMax
      apply hzT
      have hU : u.im ≤ maximumHeight u := by
        simpa only [one_smul] using im_smul_le_maximumHeight u 1
      exact mem_iUnion.mpr ⟨q, u, ⟨hu, hU.trans hMax⟩, rfl⟩
  · apply MeasurableSet.iUnion
    intro q
    exact (measurableEmbedding_const_smul (cellRepresentative H q : GL (Fin 2) ℝ)).
      measurableSet_image.mpr ModularGroup.isClosed_fd.measurableSet

theorem integrableOn_weightedCurl (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (J : ℂ → ℂ) {B : ℝ}
    (hJ : ContDiffOn ℝ 1 J {w : ℂ | 0 < w.im})
    (hSupport : ∀ z : ℍ, B < maximumHeight z → J z = 0) :
    IntegrableOn (weightedCurl J) (cosetCells H ModularGroup.fd) :=
  integrableOn_cusp_support H (weightedCurl J) (weightedCurl_continuous hJ)
    (weightedCurl_eq_zero_above hSupport)

theorem integral_compact_current_zero (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (hNeg : (-1 : SL(2, ℤ)) ∈ H) (J : ℂ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hJ : ContDiffOn ℝ 1 J {w : ℂ | 0 < w.im})
    (hSupport : ∀ z : ℍ, B < maximumHeight z → J z = 0)
    (hInv : ∀ h : SL(2, ℤ), h ∈ H →
      (fun z : ℍ => J z) ∣[(2 : ℤ)] h = fun z : ℍ => J z) :
    (∫ z in cosetCells H ModularGroup.fd, weightedCurl J z) = 0 := by
  have hB' : 1 ≤ B + 1 := by linarith
  have hTrace := trace_contDiffOn H J hJ hInv
  have hD (z : ℍ) : DifferentiableAt ℝ J z :=
    ((hJ z z.im_pos).contDiffAt (isOpen_upper.mem_nhds z.im_pos)).differentiableAt (le_refl 1)
  refine integral_global_curl_zero H hNeg J hD hInv
    (integrableOn_weightedCurl H J hJ hSupport) hB' ?_
    (traceRegularity_of_contDiffOn _ hB' hTrace)
  intro z hz
  apply trace_vanishes
  intro g
  apply hSupport
  rw [maximumHeight_invariant]
  have hU : z.im ≤ maximumHeight z := by
    simpa only [one_smul] using im_smul_le_maximumHeight z 1
  linarith [hz.trans hU]

end
end ManuscriptAudit.Paper8CompactCurrentGreen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8CompactCurrentGreen.integral_compact_current_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
