import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspSection

/-! The extended height profiles are genuine smooth sections of the theta multiplier. -/

namespace ManuscriptAudit.Paper9HighCuspSection

open Filter Set Matrix ThetaGlobalSection
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped ContDiff UpperHalfPlane MatrixGroups Pointwise Topology

noncomputable section

private def mode (w : ℂ) : ℂ := ((w.im ^ (1 / 4 : ℝ) : ℝ) : ℂ) * jacobiTheta w

private theorem mode_eq (w : ℂ) (hw : 0 < w.im) :
    mode w = thetaWeightedMode (UpperHalfPlane.ofComplex w) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  rfl

private theorem mode_smooth (w : ℂ) (hw : 0 < w.im) :
    ContDiffAt ℝ ∞ mode w := by
  have hd : DifferentiableOn ℂ jacobiTheta UpperHalfPlane.upperHalfPlaneSet :=
    fun z hz => (differentiableAt_jacobiTheta hz).differentiableWithinAt
  have hc : ContDiffOn ℂ ∞ jacobiTheta UpperHalfPlane.upperHalfPlaneSet :=
    hd.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hk := (hc.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).restrictScalars ℝ
  have hr := Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne
    (p := (1 / 4 : ℝ)) (x := w) hw.ne'
  have hcast := Complex.ofRealCLM.contDiff.contDiffAt.comp w hr
  exact hcast.mul hk

private def denominator (γ : GammaTwo) (w : ℂ) : ℂ :=
  ((((γ : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * w +
    (((γ : SL(2, ℤ)) 1 1 : ℤ) : ℂ))

private def matrixMap (γ : GammaTwo) (w : ℂ) : ℂ :=
  ((((γ : SL(2, ℤ)) 0 0 : ℤ) : ℂ) * w +
    (((γ : SL(2, ℤ)) 0 1 : ℤ) : ℂ)) / denominator γ w

private theorem denominator_ne_zero (γ : GammaTwo) (w : ℂ) (hw : 0 < w.im) :
    denominator γ w ≠ 0 := by
  let g := (γ : SL(2, ℤ))
  intro h
  have hi := congrArg Complex.im h
  change (((g 1 0 : ℤ) : ℂ) * w + ((g 1 1 : ℤ) : ℂ)).im = 0 at hi
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero] at hi
  have hc : g 1 0 = 0 := by
    exact_mod_cast (mul_eq_zero.mp hi).resolve_right hw.ne'
  have hd : g 1 1 = 0 := by
    change (((g 1 0 : ℤ) : ℂ) * w + ((g 1 1 : ℤ) : ℂ)) = 0 at h
    exact_mod_cast (by simpa [hc] using h : ((g 1 1 : ℤ) : ℂ) = 0)
  have hd' := g.det_coe
  rw [Matrix.det_fin_two, hc, hd, mul_zero, mul_zero, sub_zero] at hd'
  norm_num at hd'

private theorem matrixMap_formula (γ : GammaTwo) (w : ℂ) (hw : 0 < w.im) :
    matrixMap γ w = ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  symm
  simpa only [matrixMap, denominator] using
    (UpperHalfPlane.coe_specialLinearGroup_apply (γ : SL(2, ℤ)) (⟨w, hw⟩ : ℍ))

private theorem matrixMap_smooth (γ : GammaTwo) (w : ℂ) (hw : 0 < w.im) :
    ContDiffAt ℝ ∞ (matrixMap γ) w := by
  unfold matrixMap
  exact ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).div
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const) (denominator_ne_zero γ w hw)

theorem extendedSection_realSmooth (a : ℝ → ℂ) (ha : ContDiff ℝ ∞ a)
    (Y : ℝ) (hY : 1 ≤ Y) (hs : ∀ y, y < Y + 2 ∨ Y + 5 < y → a y = 0) :
    ContDiffOn ℝ ∞ (fun w => extendedSection a (UpperHalfPlane.ofComplex w))
      UpperHalfPlane.upperHalfPlaneSet := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  let z := UpperHalfPlane.ofComplex w
  let K := gammaTwoQuotientMk '' closedStrip Y
  have hK : IsCompact K := (closedStrip_compact Y hY).image
    gammaTwoQuotientMk_isOpenQuotientMap.continuous
  have hHw : ∀ᶠ v : ℂ in 𝓝 w, 0 < v.im :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw
  by_cases hq : gammaTwoQuotientMk z ∈ K
  · obtain ⟨u, hu, hqU⟩ := hq
    have huHigh : 1 < u.im := by
      have h := (show u.im ∈ Icc (Y + 2) (Y + 5) from hu.2).1
      linarith
    obtain ⟨γ, hγ⟩ := orbitLift hqU
    have hΓ := matrixMap_formula γ w hw
    have hW : 1 < (matrixMap γ w).im := by
      rw [hΓ]
      change 1 < (γ • z : ℍ).im
      rwa [hγ]
    have hm := matrixMap_smooth γ w hw
    have hH := Complex.imCLM.contDiff.contDiffAt.comp w hm
    have hθ := (mode_smooth (matrixMap γ w) (zero_lt_one.trans hW)).comp w hm
    have hθne : mode (matrixMap γ w) ≠ 0 := by
      rw [hΓ]
      rw [mode_eq _ (γ • z : ℍ).im_pos, UpperHalfPlane.ofComplex_apply]
      exact thetaWeightedMode_ne_zero (γ • z)
    have hform := (mode_smooth w hw).mul ((ha.contDiffAt.comp w hH).div hθ hθne)
    apply hform.congr_of_eventuallyEq
    have ht : ∀ᶠ v : ℂ in 𝓝 w, 1 < (matrixMap γ v).im :=
      hH.continuousAt (Ioi_mem_nhds hW)
    filter_upwards [hHw, ht] with v hv ht
    change extendedSection a (UpperHalfPlane.ofComplex v) =
      mode v * (a (matrixMap γ v).im / mode (matrixMap γ v))
    rw [matrixMap_formula γ v hv] at ht ⊢
    change extendedSection a (UpperHalfPlane.ofComplex v) =
      mode v * (a (γ • UpperHalfPlane.ofComplex v : ℍ).im /
        mode ((γ • UpperHalfPlane.ofComplex v : ℍ) : ℂ))
    rw [extendedSection_at_translated_high a γ _ ht, mode_eq v hv,
      mode_eq _ (γ • UpperHalfPlane.ofComplex v : ℍ).im_pos, UpperHalfPlane.ofComplex_apply]
  · have hsrc : w ∈ UpperHalfPlane.ofComplex.source := by
      change w ∈ range ((↑) : ℍ → ℂ)
      exact ⟨⟨w, hw⟩, rfl⟩
    have hOf : ContinuousAt (fun v : ℂ => UpperHalfPlane.ofComplex v) w :=
      UpperHalfPlane.ofComplex.continuousOn.continuousAt
        (UpperHalfPlane.ofComplex.open_source.mem_nhds hsrc)
    have hc := gammaTwoQuotientMk_isOpenQuotientMap.continuous.continuousAt.comp
      (x := w) hOf
    have hn : ∀ᶠ v : ℂ in 𝓝 w, gammaTwoQuotientMk (UpperHalfPlane.ofComplex v) ∉ K :=
      hc (hK.isClosed.isOpen_compl.mem_nhds hq)
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ => (0 : ℂ)) w).congr_of_eventuallyEq
    filter_upwards [hn] with v hv
    exact extendedSection_zero_outside_strip a Y hY hs (UpperHalfPlane.ofComplex v) hv

end
end ManuscriptAudit.Paper9HighCuspSection

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9HighCuspSection.extendedSection_realSmooth
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
