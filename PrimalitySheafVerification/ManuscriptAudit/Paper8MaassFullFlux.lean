import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassAdjointCurl
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCriticalFlux

/-! The full pointwise Green identity for a raised Maass field, with its exact adjoint term. -/

namespace ManuscriptAudit.Paper8MaassFullFlux

open UpperHalfPlane MaassLaplacian Paper8MaassCriticalHolomorphic
open Paper8NegativeHalfMaassFactorization Paper8MaassAdjointHolomorphic Paper8MaassAdjointCurl
open Paper8MaassCurlCalculus Paper8MaassFluxCurl Paper8MaassWirtinger Paper8CurvedCurrentGreen
open Paper8MaassGaugeDerivative Paper8MaassGaugeRaising Paper8MaassCriticalFlux

noncomputable section

private theorem height_power_shift {y : ℝ} (hy : 0 < y) (n : ℕ) :
    ((y ^ ((1 / 4 : ℝ) - (n : ℝ)) : ℝ) : ℂ) * (y : ℂ) ^ n =
      ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
  have h := Real.rpow_add hy ((1 / 4 : ℝ) - (n : ℝ)) (n : ℝ)
  rw [sub_add_cancel, Real.rpow_natCast] at h
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using congrArg Complex.ofReal h.symm

theorem complexCurl_flux_full {F G : ℂ → ℂ} {x y : ℝ} (hy : 0 < y)
    (hF : DifferentiableAt ℝ F (complexPoint x y))
    (hG : DifferentiableAt ℝ G (complexPoint x y))
    (hRaise : G (complexPoint x y) = raising (realProfile F) x y) :
    complexCurl (fluxCurrent F G) (complexPoint x y) =
      -((‖G (complexPoint x y)‖ ^ 2 / y ^ 2 : ℝ) : ℂ) +
        (starRingEnd ℂ) (F (complexPoint x y)) *
          adjointExpression (realProfile G) x y / (y : ℂ) ^ 2 := by
  let w := complexPoint x y
  let z : ℍ := ⟨w, by simpa only [w, complexPoint_im] using hy⟩
  let B := complexGaugeRatio F
  let H (q : ℂ) := ModularForm.eta q * adjointPartner G q
  let C : ℂ →+* ℂ := starRingEnd ℂ
  let a := complexGauge w
  let Q : ℂ := (y ^ (1 / 4 : ℝ) : ℝ)
  let D : ℂ := (y ^ (-(3 / 4 : ℝ)) : ℝ)
  let E : ℂ := (y ^ (-(7 / 4 : ℝ)) : ℝ)
  let d := derivativeZ B w
  let Y : ℂ := y
  let K := adjointExpression (realProfile G) x y
  have hPos : 0 < w.im := z.im_pos
  have hb : DifferentiableAt ℝ B w := complexGaugeRatio_differentiableAt z hF
  have hbC : DifferentiableAt ℝ (fun q => C (B q)) w :=
    Complex.differentiable_conj.differentiableAt.comp w hb
  have hHeight : DifferentiableAt ℝ (fun q : ℂ => ((q.im ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ)) w :=
    ((Real.hasDerivAt_rpow_const (p := -(3 / 4 : ℝ)) (Or.inl hPos.ne')).ofReal_comp.differentiableAt.comp
      w Complex.imCLM.differentiableAt
  have hEta := ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hPos
  have hH : DifferentiableAt ℝ H w := (hEta.restrictScalars ℝ).mul (hHeight.mul hG)
  have hBcurl : complexCurl (fun q => C (B q)) w = 2 * Complex.I * C d := by
    have h := curl_conj_mul_holomorphic (H := fun _ : ℂ => (1 : ℂ)) hb (differentiableAt_const _)
    simpa only [mul_one, curl, complexCurl, C, d, w] using h
  have hHcurl : complexCurl H w = ModularForm.eta w * E * K :=
    complexCurl_eta_adjointPartner hy hG
  have hA : C a = Q * ModularForm.eta w := by
    simp only [C, a, Q, complexGauge, w, complexPoint_im, map_mul, Complex.conj_ofReal,
      starRingEnd_self_apply]
  have hY : Y ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hQ : Q ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hy _).ne'
  have hEta0 : ModularForm.eta w ≠ 0 := ModularForm.eta_ne_zero hPos
  have hC0 : C a ≠ 0 := by rw [hA]; exact mul_ne_zero hQ hEta0
  have hDY : D * Y = Q := by
    have h := height_power_shift hy 1
    simpa only [show (1 / 4 : ℝ) - (1 : ℕ) = -(3 / 4 : ℝ) by norm_num, Nat.cast_one,
      pow_one, D, Y, Q] using h
  have hEY : E * Y ^ 2 = Q := by
    have h := height_power_shift hy 2
    simpa only [show (1 / 4 : ℝ) - (2 : ℕ) = -(7 / 4 : ℝ) by norm_num, Nat.cast_ofNat,
      E, Y, Q] using h
  have hGformula : G w = 2 * Complex.I * Y * a * d :=
    hRaise.trans (raising_eq_gauge_derivativeZ x y hy hF)
  have hConjG : C (G w) = -(2 * Complex.I * Y * C a * C d) := by
    rw [hGformula]
    simp only [C, map_mul, map_ofNat, Complex.conj_I, Y, Complex.conj_ofReal]
    ring
  have hHvalue : H w = ModularForm.eta w * (D * G w) := by simp only [H, adjointPartner, D, w, complexPoint_im]
  have hEne : complexCurl (fun q => C (B q)) w * H w = -((‖G w‖ ^ 2 / y ^ 2 : ℝ) : ℂ) := by
    have hFactor : ModularForm.eta w * D = C a / Y := by
      apply (eq_div_iff hY).2
      rw [hA, mul_assoc, hDY, mul_comm]
    rw [hBcurl, hHvalue, ← mul_assoc (ModularForm.eta w), hFactor]
    have hNorm : C (G w) * G w = ((‖G w‖ : ℝ) : ℂ) ^ 2 := by
      simpa only [C, Complex.ofReal_pow] using Complex.conj_mul' (G w)
    simp only [Complex.ofReal_div, Complex.ofReal_pow]
    rw [← hNorm, hConjG]
    field_simp [hY] <;> ring
  have hAdj : C (B w) * complexCurl H w = C (F w) * K / Y ^ 2 := by
    have hFactor : (ModularForm.eta w * E) / C a = 1 / Y ^ 2 := by
      apply (div_eq_div_iff hC0 (pow_ne_zero 2 hY)).2
      rw [mul_assoc, hEY, hA, one_mul, mul_comm]
    rw [hHcurl]
    change C (F w / a) * (ModularForm.eta w * E * K) = _
    rw [map_div₀]
    calc
      _ = C (F w) * K * ((ModularForm.eta w * E) / C a) := by ring
      _ = _ := by rw [hFactor]; ring
  change complexCurl (fun q => C (B q) * H q) w = _
  rw [complexCurl_mul hbC hH, hAdj, hEne]
  ring

end
end ManuscriptAudit.Paper8MaassFullFlux

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassFullFlux.complexCurl_flux_full
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
