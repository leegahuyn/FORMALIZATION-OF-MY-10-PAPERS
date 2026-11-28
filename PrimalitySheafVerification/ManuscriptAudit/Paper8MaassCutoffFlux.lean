import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCriticalFlux
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCurlCalculus
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCutoffDerivative

/-! Exact cutoff energy identity and the pointwise cusp-tail error bound for the Maass flux. -/

namespace ManuscriptAudit.Paper8MaassCutoffFlux

open Set UpperHalfPlane MaassLaplacian
open Paper8MaassCriticalHolomorphic Paper8NegativeHalfMaassFactorization
open Paper8MaassCriticalFlux Paper8MaassAdjointHolomorphic Paper8MaassGaugeDerivative
open Paper8MaassCutoffTaper Paper8MaassCutoffDerivative Paper8MaassWirtinger
open Paper8MaassCurlCalculus Paper8CurvedCurrentGreen Paper8ModularHeightCutoff

noncomputable section

def cutoffFlux (Y : ℝ) (F G : ℂ → ℂ) (w : ℂ) : ℂ :=
  complexCutoff Y w ^ 2 * fluxCurrent F G w

def cutoffError (Y : ℝ) (F G : ℂ → ℂ) (w : ℂ) : ℂ :=
  4 * Complex.I * complexCutoff Y w * (starRingEnd ℂ) (derivativeZ (complexCutoff Y) w) *
    fluxCurrent F G w

theorem norm_fluxCurrent (F G : ℂ → ℂ) (z : ℍ) :
    ‖fluxCurrent F G z‖ = ‖F z‖ * ‖G z‖ / z.im := by
  have hA : 0 < z.im ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos z.im_pos _
  have hB : 0 < z.im ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos z.im_pos _
  have hEta : ‖ModularForm.eta z‖ ≠ 0 := norm_ne_zero_iff.mpr (ModularForm.eta_ne_zero z.im_pos)
  have hScale : z.im ^ (-(3 / 4 : ℝ)) = z.im ^ (1 / 4 : ℝ) / z.im := by
    have h := Real.rpow_sub z.im_pos (1 / 4) 1
    rw [show (1 / 4 : ℝ) - 1 = -(3 / 4 : ℝ) by ring, Real.rpow_one] at h
    exact h
  simp only [fluxCurrent, complexGaugeRatio, complexGauge, adjointPartner, UpperHalfPlane.coe_im,
    Complex.norm_conj, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA,
    abs_of_pos hB, hScale]
  field_simp [z.im_pos.ne', hEta, hA.ne'] <;> ring

theorem cutoffError_zero_below {Y : ℝ} (hY : 2 < Y) (F G : ℂ → ℂ) (z : ℍ)
    (hz : maximumHeight z < Y) : cutoffError Y F G z = 0 := by
  simp only [cutoffError, complexCutoff_derivativeZ_zero_below hY z hz, map_zero, mul_zero, zero_mul]

theorem cutoffError_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y > 2, ∀ (F G : ℂ → ℂ) (z : ℍ),
      ‖cutoffError Y F G z‖ ≤ C * ‖complexCutoff Y z‖ * ‖F z‖ * ‖G z‖ / z.im ^ 2 := by
  obtain ⟨C, hC, hD⟩ := complexCutoff_derivativeZ_uniform
  refine ⟨2 * C, by positivity, fun Y hY F G z => ?_⟩
  have hd : ‖derivativeZ (complexCutoff Y) z‖ ≤ C / (2 * z.im) :=
    (le_div_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hD Y hY z)
  have hFour : ‖(4 : ℂ)‖ = 4 := by norm_num
  simp only [cutoffError, norm_mul, hFour, Complex.norm_I, mul_one, Complex.norm_conj]
  rw [norm_fluxCurrent]
  calc
    _ ≤ 4 * ‖complexCutoff Y z‖ * (C / (2 * z.im)) * (‖F z‖ * ‖G z‖ / z.im) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) (by positivity)
    _ = _ := by field_simp [z.im_pos.ne'] <;> ring

theorem cutoffFlux_curl {Y : ℝ} (hY : 2 < Y) {F G : ℂ → ℂ}
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0)
    (x y : ℝ) (hy : 0 < y) :
    curl (cutoffFlux Y F G) x y =
      -complexCutoff Y (complexPoint x y) ^ 2 *
        ((‖raising (realProfile F) x y‖ ^ 2 / y ^ 2 : ℝ) : ℂ) +
        cutoffError Y F G (complexPoint x y) := by
  let w := complexPoint x y
  let z : ℍ := ⟨w, by simpa only [w, complexPoint_im] using hy⟩
  have hPos : 0 < w.im := z.im_pos
  have hOpen : IsOpen {v : ℂ | 0 < v.im} := isOpen_lt continuous_const Complex.continuous_im
  have hSmooth := ((modularCutoff_real_smooth hY) w hPos).contDiffAt (hOpen.mem_nhds hPos)
  have hChiReal : DifferentiableAt ℝ (fun v : ℂ => modularCutoff Y (ofComplex v)) w :=
    hSmooth.differentiableAt (by simp)
  have hChi : DifferentiableAt ℝ (complexCutoff Y) w :=
    Complex.ofRealCLM.differentiableAt.comp w hChiReal
  have hB : DifferentiableAt ℝ (complexGaugeRatio F) w :=
    complexGaugeRatio_differentiableAt z (hF w hPos)
  have hH : DifferentiableAt ℂ (fun v => ModularForm.eta v * adjointPartner G v) w :=
    ((adjointGaugeProduct_differentiableOn hG hAdj) w hPos).differentiableAt (hOpen.mem_nhds hPos)
  have hJ : DifferentiableAt ℝ (fluxCurrent F G) w :=
    (Complex.differentiable_conj.differentiableAt.comp _ hB).mul (hH.restrictScalars ℝ)
  have hC : complexCurl (complexCutoff Y) w =
      2 * Complex.I * (starRingEnd ℂ) (derivativeZ (complexCutoff Y) w) :=
    complexCurl_ofReal hChiReal
  have hC2 : complexCurl (fun v => complexCutoff Y v ^ 2) w =
      4 * Complex.I * complexCutoff Y w * (starRingEnd ℂ) (derivativeZ (complexCutoff Y) w) := by
    simp only [pow_two, complexCurl_mul hChi hChi, hC]
    ring
  have hKick : complexCurl (fluxCurrent F G) w =
      -((‖raising (realProfile F) x y‖ ^ 2 / y ^ 2 : ℝ) : ℂ) :=
    fluxCurl_eq_negative_energy hF hG hRaise hAdj x y hy
  change complexCurl (fun v => complexCutoff Y v ^ 2 * fluxCurrent F G v) w = _
  rw [complexCurl_mul (hChi.pow 2) hJ, hC2, hKick]
  change _ = -complexCutoff Y w ^ 2 * ((‖raising (realProfile F) x y‖ ^ 2 / y ^ 2 : ℝ) : ℂ) +
    cutoffError Y F G w
  unfold cutoffError
  ring

end
end ManuscriptAudit.Paper8MaassCutoffFlux

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassCutoffFlux.norm_fluxCurrent,
      ``ManuscriptAudit.Paper8MaassCutoffFlux.cutoffError_uniform,
      ``ManuscriptAudit.Paper8MaassCutoffFlux.cutoffFlux_curl] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
