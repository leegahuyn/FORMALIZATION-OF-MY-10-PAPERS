import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassFluxCurl
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassAdjointHolomorphic
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassGaugeCurrent
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassGaugeRaising

/-! The exact critical odd Maass Green current has curl equal to negative raising energy. -/

namespace ManuscriptAudit.Paper8MaassCriticalFlux

open Set UpperHalfPlane MaassLaplacian Paper8NegativeHalfMaassFactorization
open Paper8MaassCriticalHolomorphic Paper8MaassAdjointHolomorphic
open Paper8MaassGaugeDerivative Paper8MaassGaugeCurrent Paper8MaassGaugeRaising
open Paper8MaassWirtinger Paper8MaassFluxCurl Paper8CurvedCurrentGreen

noncomputable section

def fluxCurrent (F G : ℂ → ℂ) (w : ℂ) : ℂ :=
  (starRingEnd ℂ) (complexGaugeRatio F w) * (ModularForm.eta w * adjointPartner G w)

private theorem adjointGauge_eq_derivativeZ {F G : ℂ → ℂ} {x y : ℝ} (hy : 0 < y)
    (hF : DifferentiableAt ℝ F (complexPoint x y))
    (hRaise : G (complexPoint x y) = raising (realProfile F) x y) :
    ModularForm.eta (complexPoint x y) * adjointPartner G (complexPoint x y) =
      2 * Complex.I * (gaugeSquare ⟨complexPoint x y, by simpa only [complexPoint_im] using hy⟩ : ℂ) *
        derivativeZ (complexGaugeRatio F) (complexPoint x y) := by
  let w := complexPoint x y
  let z : ℍ := ⟨w, by simpa only [w, complexPoint_im] using hy⟩
  let a := complexGauge w
  let A : ℂ := (y ^ (1 / 4 : ℝ) : ℝ)
  let B : ℂ := (y ^ (-(3 / 4 : ℝ)) : ℝ)
  let d := derivativeZ (complexGaugeRatio F) w
  have hH : B * (y : ℂ) = A := by
    have h := Real.rpow_add hy (-(3 / 4 : ℝ)) 1
    rw [show (-(3 / 4 : ℝ)) + 1 = 1 / 4 by ring, Real.rpow_one] at h
    simpa only [A, B, Complex.ofReal_mul] using congrArg Complex.ofReal h.symm
  have hConj : (starRingEnd ℂ) a = A * ModularForm.eta w := by
    simp only [a, A, complexGauge, w, complexPoint_im, map_mul, Complex.conj_ofReal,
      starRingEnd_self_apply]
  have hA : a * (A * ModularForm.eta w) = (gaugeSquare z : ℂ) := by
    rw [← hConj]
    have hNorm : ‖a‖ ^ 2 = gaugeSquare z := by
      unfold gaugeSquare
      change ‖complexGauge (z : ℂ)‖ ^ 2 = _
      rw [complexGauge_coe]
    simpa only [← Complex.ofReal_pow, hNorm] using Complex.mul_conj' a
  conv_lhs => rw [adjointPartner, complexPoint_im, hRaise, raising_eq_gauge_derivativeZ x y hy hF]
  change ModularForm.eta w * (B * (2 * Complex.I * (y : ℂ) * a * d)) = _
  calc
    _ = 2 * Complex.I * (a * ((B * (y : ℂ)) * ModularForm.eta w)) * d := by ring
    _ = _ := by rw [hH, hA]

theorem fluxCurrent_coe_eq {F G : ℂ → ℂ}
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (z : ℍ) :
    fluxCurrent F G z = 2 * Complex.I * currentCoefficient F z := by
  have hPoint : complexPoint z.re z.im = (z : ℂ) := Complex.re_add_im z
  have hDiff : DifferentiableAt ℝ F (complexPoint z.re z.im) := by rw [hPoint]; exact hF z z.im_pos
  have h := adjointGauge_eq_derivativeZ z.im_pos hDiff (hRaise z.re z.im z.im_pos)
  have hz : (⟨complexPoint z.re z.im, by simp [z.im_pos]⟩ : ℍ) = z := UpperHalfPlane.ext hPoint
  change ModularForm.eta (complexPoint z.re z.im) * adjointPartner G (complexPoint z.re z.im) =
    2 * Complex.I * (gaugeSquare ⟨complexPoint z.re z.im, by simp [z.im_pos]⟩ : ℂ) *
      derivativeZ (complexGaugeRatio F) (complexPoint z.re z.im) at h
  rw [hz, hPoint] at h
  rw [fluxCurrent, h, currentCoefficient]
  ring

theorem fluxCurl_eq_negative_energy {F G : ℂ → ℂ}
    (hF : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ F w)
    (hG : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℝ G w)
    (hRaise : ∀ x y : ℝ, 0 < y → G (complexPoint x y) = raising (realProfile F) x y)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0)
    (x y : ℝ) (hy : 0 < y) :
    curl (fluxCurrent F G) x y = -((‖raising (realProfile F) x y‖ ^ 2 / y ^ 2 : ℝ) : ℂ) := by
  let w := complexPoint x y
  let z : ℍ := ⟨w, by simpa only [w, complexPoint_im] using hy⟩
  let d := derivativeZ (complexGaugeRatio F) w
  have hPos : 0 < w.im := by simpa only [w, complexPoint_im] using hy
  have hDiff : DifferentiableAt ℝ F w := hF w hPos
  have hB : DifferentiableAt ℝ (complexGaugeRatio F) w := complexGaugeRatio_differentiableAt z hDiff
  have hOpen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hH : DifferentiableAt ℂ (fun v => ModularForm.eta v * adjointPartner G v) w :=
    ((adjointGaugeProduct_differentiableOn hG hAdj) w hPos).differentiableAt (hOpen.mem_nhds hPos)
  have hd : ModularForm.eta w * adjointPartner G w = 2 * Complex.I * (gaugeSquare z : ℂ) * d :=
    adjointGauge_eq_derivativeZ hy hDiff (hRaise x y hy)
  have hA : ‖complexGauge w‖ ^ 2 = gaugeSquare z := by
    change ‖complexGauge (z : ℂ)‖ ^ 2 = _
    rw [complexGauge_coe, gaugeSquare]
  have hEnergy : ‖raising (realProfile F) x y‖ ^ 2 / y ^ 2 = 4 * gaugeSquare z * ‖d‖ ^ 2 := by
    rw [raising_eq_gauge_derivativeZ x y hy hDiff]
    change ‖2 * Complex.I * (y : ℂ) * complexGauge w * d‖ ^ 2 / y ^ 2 = _
    have hTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy,
      hTwo, mul_one, mul_pow, hA]
    field_simp [hy.ne'] <;> ring
  unfold fluxCurrent
  rw [curl_conj_mul_holomorphic hB hH, hEnergy]
  change 2 * Complex.I * (starRingEnd ℂ) d * (ModularForm.eta w * adjointPartner G w) = _
  rw [hd]
  calc
    _ = 4 * Complex.I ^ 2 * (gaugeSquare z : ℂ) * ((starRingEnd ℂ) d * d) := by ring
    _ = _ := by
      rw [Complex.I_sq, Complex.conj_mul']
      push_cast <;> ring

end
end ManuscriptAudit.Paper8MaassCriticalFlux

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassCriticalFlux.fluxCurrent_coe_eq,
      ``ManuscriptAudit.Paper8MaassCriticalFlux.fluxCurl_eq_negative_energy] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
