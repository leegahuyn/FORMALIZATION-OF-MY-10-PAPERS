import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.FDeriv.Congr
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassTraceIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper8StandardDomainCurlMeasure
import PrimalitySheafVerification.ManuscriptAudit.Paper8StandardDomainCurrentGreen

/-! Global Green on the true coset domain, constructed from native trace and side pairing. -/

namespace ManuscriptAudit.Paper8GlobalWeightTwoGreen

open Filter Function Set MeasureTheory UpperHalfPlane ModularForm MaassLaplacian
open Paper8MaassCurlCalculus Paper8MaassTraceCurl Paper8MaassTraceIntegral Paper8EtaCosetMass
open Paper8WeightTwoCosetTrace Paper8StandardDomainSidePairing
open Paper8StandardDomainCurrentGreen Paper8StandardDomainCurlMeasure
open Paper8CurvedGreenChart Paper8CurvedCurrentGreen RectangularIntegral
open scoped MatrixGroups ModularForm Topology Interval

noncomputable section

structure TraceRegularity (f : ℍ → ℂ) (B : ℝ) : Prop where
  curlContinuous : ContinuousOn (complexCurl (asComplexCurrent f))
    (((↑) : ℍ → ℂ) '' ModularGroup.truncatedFundamentalDomain B)
  pointDifferentiable : ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ∀ t ∈ Icc (0 : ℝ) 1,
    DifferentiableAt ℝ (asComplexCurrent f) (point arcHeight B x t)
  rateXContinuous : ContinuousOn (rateX (asComplexCurrent f) arcHeight B).uncurry
    (rectangle (-(1 / 2)) (1 / 2) 0 1)
  rateTContinuous : ContinuousOn (rateT (asComplexCurrent f) arcHeight B).uncurry
    (rectangle (-(1 / 2)) (1 / 2) 0 1)

theorem integral_global_curl_zero (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]
    (hNeg : (-1 : SL(2, ℤ)) ∈ H) (J : ℂ → ℂ)
    (hJ : ∀ z : ℍ, DifferentiableAt ℝ J z)
    (hInv : ∀ h : SL(2, ℤ), h ∈ H →
      (fun z : ℍ => J z) ∣[(2 : ℤ)] h = fun z : ℍ => J z)
    (hInt : IntegrableOn (weightedCurl J) (cosetCells H ModularGroup.fd))
    {B : ℝ} (hB : 1 ≤ B)
    (hTop : ∀ z : ℍ, B ≤ z.im → trace H (fun u : ℍ => J u) hInv z = 0)
    (hReg : TraceRegularity (trace H (fun u : ℍ => J u) hInv) B) :
    (∫ z in cosetCells H ModularGroup.fd, weightedCurl J z) = 0 := by
  let f := trace H (fun u : ℍ => J u) hInv
  let K := asComplexCurrent f
  have hAbove (z : ℍ) (hZ : B < z.im) : weightedCurl K z = 0 := by
    have hLocal : K =ᶠ[𝓝 (z : ℂ)] (fun _ : ℂ => (0 : ℂ)) := by
      filter_upwards [Complex.continuous_im.continuousAt.tendsto.eventually (Ioi_mem_nhds hZ)] with w hw
      have hPos : 0 < w.im := (zero_lt_one.trans_le hB).trans hw
      change f (ofComplex w) = 0
      rw [ofComplex_apply_of_im_pos hPos]
      exact hTop ⟨w, hPos⟩ hw.le
    unfold weightedCurl complexCurl
    rw [hLocal.fderiv_eq (𝕜 := ℝ), fderiv_const]
    simp
  have hFdo : (∫ z in ModularGroup.fd, weightedCurl K z) =
      ∫ z in ModularGroup.truncatedFundamentalDomain B, weightedCurl K z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ModularGroup.isClosed_fd.measurableSet
      (fun _ hz => hz.1)
    intro z hz
    have hZ : B < z.im := lt_of_not_ge (fun h => hz.2 ⟨hz.1, h⟩)
    exact hAbove z hZ
  have hZero := integral_curl_zero f hB
    (trace_slash H (fun u : ℍ => J u) hInv ModularGroup.T)
    (trace_slash H (fun u : ℍ => J u) hInv ModularGroup.S)
    (fun x _ => by
      have hPos : 0 < (complexPoint x B).im := by rw [complexPoint_im]; exact zero_lt_one.trans_le hB
      rw [ofComplex_apply_of_im_pos hPos]
      exact hTop ⟨complexPoint x B, hPos⟩ (by change B ≤ (complexPoint x B).im; rw [complexPoint_im]))
    hReg.pointDifferentiable hReg.rateXContinuous hReg.rateTContinuous
  calc
    _ = ∫ z in ModularGroup.fd, weightedCurl K z :=
      (integral_weightedCurl_trace_closed H hNeg J hJ hInv hInt).symm
    _ = ∫ z in ModularGroup.truncatedFundamentalDomain B, weightedCurl K z := hFdo
    _ = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), ∫ y in arcHeight x..B, curl K x y :=
      integral_truncated_weightedCurl K hB hReg.curlContinuous
    _ = _ := hZero

end
end ManuscriptAudit.Paper8GlobalWeightTwoGreen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8GlobalWeightTwoGreen.integral_global_curl_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
