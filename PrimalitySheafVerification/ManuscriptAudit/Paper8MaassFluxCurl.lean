import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8CurvedCurrentGreen
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassWirtinger
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCriticalHolomorphic

/-! Exterior derivative of a conjugate-real-smooth function times a holomorphic factor. -/

namespace ManuscriptAudit.Paper8MaassFluxCurl

open Function MaassLaplacian Paper8MaassCriticalHolomorphic
open Paper8CurvedCurrentGreen Paper8MaassWirtinger

noncomputable section

private theorem curl_eq_partials {J : ℂ → ℂ} {x y : ℝ}
    (hJ : DifferentiableAt ℝ J (complexPoint x y)) :
    curl J x y = Complex.I * partialX (realProfile J) x y - partialY (realProfile J) x y := by
  have hX : HasDerivAt (fun t => complexPoint t y) (1 : ℂ) x := by
    simpa only [id_eq] using horizontal_derivative (hasDerivAt_id (complexPoint x y))
  have hY : HasDerivAt (fun t => complexPoint x t) Complex.I y := by
    simpa only [id_eq, mul_one] using vertical_derivative (hasDerivAt_id (complexPoint x y))
  have hDx : partialX (realProfile J) x y = fderiv ℝ J (complexPoint x y) 1 :=
    (hJ.hasFDerivAt.comp_hasDerivAt x hX).deriv
  have hDy : partialY (realProfile J) x y = fderiv ℝ J (complexPoint x y) Complex.I :=
    (hJ.hasFDerivAt.comp_hasDerivAt y hY).deriv
  rw [hDx, hDy, curl]

private theorem conjugate_derivative {f : ℝ → ℂ} {d : ℂ} {x : ℝ} (h : HasDerivAt f d x) :
    HasDerivAt (fun t => (starRingEnd ℂ) (f t)) ((starRingEnd ℂ) d) x :=
  Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x h

theorem curl_conj_mul_holomorphic {B H : ℂ → ℂ} {x y : ℝ}
    (hB : DifferentiableAt ℝ B (complexPoint x y))
    (hH : DifferentiableAt ℂ H (complexPoint x y)) :
    curl (fun w => (starRingEnd ℂ) (B w) * H w) x y =
      2 * Complex.I * (starRingEnd ℂ) (derivativeZ B (complexPoint x y)) *
        H (complexPoint x y) := by
  let w := complexPoint x y
  let J (z : ℂ) := (starRingEnd ℂ) (B z) * H z
  let c : ℂ →+* ℂ := starRingEnd ℂ
  let d := deriv H w
  have hJ : DifferentiableAt ℝ J w :=
    (Complex.differentiable_conj.differentiableAt.comp _ hB).mul (hH.restrictScalars ℝ)
  have hHx : HasDerivAt (fun t : ℝ => H (complexPoint t y)) d x :=
    horizontal_derivative hH.hasDerivAt
  have hHy : HasDerivAt (fun t : ℝ => H (complexPoint x t)) (Complex.I * d) y :=
    vertical_derivative hH.hasDerivAt
  have hDx : partialX (realProfile J) x y =
      c (partialX (realProfile B) x y) * H w + c (B w) * d := by
    have hFun : (fun t : ℝ => realProfile J t y) =
        (fun t : ℝ => c (realProfile B t y)) * (fun t : ℝ => H (complexPoint t y)) := by
      funext t
      rfl
    unfold partialX
    rw [hFun]
    exact ((conjugate_derivative (profile_horizontal hB)).mul hHx).deriv
  have hDy : partialY (realProfile J) x y =
      c (partialY (realProfile B) x y) * H w + c (B w) * (Complex.I * d) := by
    have hFun : realProfile J x =
        (fun t : ℝ => c (realProfile B x t)) * (fun t : ℝ => H (complexPoint x t)) := by
      funext t
      rfl
    unfold partialY
    rw [hFun]
    exact ((conjugate_derivative (profile_vertical hB)).mul hHy).deriv
  change curl J x y = 2 * Complex.I * c (derivativeZ B w) * H w
  rw [curl_eq_partials hJ, hDx, hDy, derivativeZ_eq_partials hB]
  change Complex.I * (c (partialX (realProfile B) x y) * H w + c (B w) * d) -
    (c (partialY (realProfile B) x y) * H w + c (B w) * (Complex.I * d)) =
    2 * Complex.I * c ((partialX (realProfile B) x y -
      Complex.I * partialY (realProfile B) x y) / 2) * H w
  simp only [map_div₀, map_sub, map_mul, map_ofNat, c, Complex.conj_I]
  linear_combination -((starRingEnd ℂ) (partialY (realProfile B) x y) * H w) * Complex.I_sq

end
end ManuscriptAudit.Paper8MaassFluxCurl

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassFluxCurl.curl_conj_mul_holomorphic
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
