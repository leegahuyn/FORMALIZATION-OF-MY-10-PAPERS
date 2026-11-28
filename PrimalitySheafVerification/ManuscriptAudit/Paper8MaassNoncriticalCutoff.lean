import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassFullFlux
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGlobalCutoffGreen

/-! Exact cutoff identity at an arbitrary shifted eigenvalue for the genuine odd Maass problem. -/

namespace ManuscriptAudit.Paper8MaassNoncriticalCutoff

open Set UpperHalfPlane MaassLaplacian
open Paper8MaassTraceCurl Paper8MaassCurlCalculus Paper8MaassWirtinger
open Paper8MaassAdjointHolomorphic Paper8MaassCriticalFlux Paper8MaassFullFlux
open Paper8MaassCriticalHolomorphic Paper8NegativeHalfMaassFactorization Paper8MaassGaugeDerivative
open Paper8MaassCutoffTaper Paper8MaassCutoffDerivative Paper8MaassCutoffFlux Paper8OddGlobalCutoffGreen

noncomputable section

theorem weightedCurl_cutoffFlux_eq_shifted_energy {Y δ : ℝ} (hY : 2 < Y) {F G : ℂ → ℂ}
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = (δ : ℂ) * realProfile F x y)
    (z : ℍ) :
    weightedCurl (cutoffFlux Y F G) z =
      -(cutoffEnergy Y G z : ℂ) +
      (δ : ℂ) * (cutoffEnergy Y F z : ℂ) + weightedCutoffError Y F G z := by
  let w := (z : ℂ)
  have hPoint : complexPoint z.re z.im = w := Complex.re_add_im z
  have hz : 0 < w.im := z.im_pos
  have hU : IsOpen {v : ℂ | 0 < v.im} := isOpen_lt continuous_const Complex.continuous_im
  have hSmooth := ((modularCutoff_real_smooth hY) w hz).contDiffAt (hU.mem_nhds hz)
  have hChiR : DifferentiableAt ℝ (fun v : ℂ => modularCutoff Y (ofComplex v)) w :=
    hSmooth.differentiableAt (by simp)
  have hChi : DifferentiableAt ℝ (complexCutoff Y) w :=
    Complex.ofRealCLM.differentiableAt.comp w hChiR
  have hB : DifferentiableAt ℝ (complexGaugeRatio F) w :=
    complexGaugeRatio_differentiableAt z (hF w hz)
  have hHeight : DifferentiableAt ℝ (fun q : ℂ => ((q.im ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ)) w :=
    (Real.hasDerivAt_rpow_const (p := -(3 / 4 : ℝ)) (Or.inl hz.ne')).ofReal_comp.differentiableAt.comp
      w Complex.imCLM.differentiableAt
  have hEta := ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz
  have hG' : DifferentiableAt ℝ (adjointPartner G) w := hHeight.mul (hG w hz)
  have hJ : DifferentiableAt ℝ (fluxCurrent F G) w :=
    (Complex.differentiable_conj.differentiableAt.comp w hB).mul
      ((hEta.restrictScalars ℝ).mul hG')
  have hC : complexCurl (complexCutoff Y) w =
      2 * Complex.I * (starRingEnd ℂ) (derivativeZ (complexCutoff Y) w) := complexCurl_ofReal hChiR
  have hC2 : complexCurl (fun v => complexCutoff Y v ^ 2) w =
      4 * Complex.I * complexCutoff Y w * (starRingEnd ℂ) (derivativeZ (complexCutoff Y) w) := by
    simp only [pow_two, complexCurl_mul hChi hChi, hC]
    ring
  have hJcurl : complexCurl (fluxCurrent F G) w =
      -((‖G w‖ ^ 2 / z.im ^ 2 : ℝ) : ℂ) +
        (starRingEnd ℂ) (F w) * ((δ : ℂ) * F w) / (z.im : ℂ) ^ 2 := by
    have hF' : DifferentiableAt ℝ F (complexPoint z.re z.im) := by rw [hPoint]; exact hF w hz
    have hG'' : DifferentiableAt ℝ G (complexPoint z.re z.im) := by rw [hPoint]; exact hG w hz
    have h := complexCurl_flux_full z.im_pos hF' hG'' (hRaise z.re z.im z.im_pos)
    rw [hAdj z.re z.im z.im_pos] at h
    simpa only [realProfile, hPoint] using h
  have hNorm : (starRingEnd ℂ) (F w) * F w = (‖F w‖ : ℂ) ^ 2 := by
    simpa only [Complex.ofReal_pow] using Complex.conj_mul' (F w)
  unfold weightedCurl cutoffFlux
  have hChiSq : DifferentiableAt ℝ (fun v => complexCutoff Y v ^ 2) w := hChi.pow 2
  rw [complexCurl_mul hChiSq hJ, hC2, hJcurl]
  unfold cutoffEnergy weightedCutoffError cutoffError
  have hChiZ : complexCutoff Y w = (modularCutoff Y z : ℂ) := complexCutoff_coe Y z
  simp only [hChiZ, complexCutoff_coe]
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul]
  rw [show (starRingEnd ℂ) (F w) * ((δ : ℂ) * F w) = (δ : ℂ) * (‖F w‖ : ℂ) ^ 2 by
    rw [← hNorm]; ring]
  dsimp only [w]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne'] <;> ring

end
end ManuscriptAudit.Paper8MaassNoncriticalCutoff

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassNoncriticalCutoff.weightedCurl_cutoffFlux_eq_shifted_energy
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
