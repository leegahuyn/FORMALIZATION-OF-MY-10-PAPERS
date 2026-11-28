import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassAdjointHolomorphic
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCurlCalculus

/-! The exact error term for the eta-gauged adjoint field away from the critical eigenspace. -/

namespace ManuscriptAudit.Paper8MaassAdjointCurl

open MaassLaplacian Paper8MaassCriticalHolomorphic Paper8NegativeHalfMaassFactorization
open Paper8MaassAdjointHolomorphic Paper8MaassCurlCalculus

noncomputable section

theorem complexCurl_adjointPartner {G : ℂ → ℂ} {x y : ℝ} (hy : 0 < y)
    (hG : DifferentiableAt ℝ G (complexPoint x y)) :
    complexCurl (adjointPartner G) (complexPoint x y) =
      ((y ^ (-(7 / 4 : ℝ)) : ℝ) : ℂ) * adjointExpression (realProfile G) x y := by
  let w := complexPoint x y
  let A (q : ℂ) : ℂ := (q.im ^ (-(3 / 4 : ℝ)) : ℝ)
  let a : ℂ := (y ^ (-(3 / 4 : ℝ)) : ℝ)
  let b : ℂ := (y ^ (-(7 / 4 : ℝ)) : ℝ)
  have hw : w.im = y := complexPoint_im x y
  have hHeight : HasDerivAt (fun t : ℝ => ((t ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ))
      (-(3 / 4 : ℂ) * b) w.im := by
    rw [hw]
    have hP : -(3 / 4 : ℝ) - 1 = -(7 / 4 : ℝ) := by norm_num
    simpa only [hP, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, b]
      using (Real.hasDerivAt_rpow_const (p := -(3 / 4 : ℝ)) (Or.inl hy.ne')).ofReal_comp
  have hD := hHeight.hasFDerivAt.comp w Complex.imCLM.hasFDerivAt
  have hA : DifferentiableAt ℝ A w := hD.differentiableAt
  have hDA : fderiv ℝ A w = _ := hD.fderiv
  have hX : fderiv ℝ A w 1 = 0 := by
    rw [hDA]
    change (0 : ℝ) • (-(3 / 4 : ℂ) * b) = 0
    exact zero_smul _ _
  have hY : fderiv ℝ A w Complex.I = -(3 / 4 : ℂ) * b := by
    rw [hDA]
    change (1 : ℝ) • (-(3 / 4 : ℂ) * b) = _
    exact one_smul _ _
  have hPointX : HasDerivAt (fun t => complexPoint t y) 1 x := by
    simpa only [id_eq] using horizontal_derivative (hasDerivAt_id w)
  have hPointY : HasDerivAt (fun t => complexPoint x t) Complex.I y := by
    simpa only [id_eq, mul_one] using vertical_derivative (hasDerivAt_id w)
  have hGX : partialX (realProfile G) x y = fderiv ℝ G w 1 :=
    (hG.hasFDerivAt.comp_hasDerivAt x hPointX).deriv
  have hGY : partialY (realProfile G) x y = fderiv ℝ G w Complex.I :=
    (hG.hasFDerivAt.comp_hasDerivAt y hPointY).deriv
  have hAB : a = (y : ℂ) * b := by
    have h := Real.rpow_add hy 1 (-(7 / 4 : ℝ))
    rw [show (1 : ℝ) + -(7 / 4 : ℝ) = -(3 / 4 : ℝ) by norm_num, Real.rpow_one] at h
    simpa only [a, b, Complex.ofReal_mul] using congrArg Complex.ofReal h
  have hA0 : A w = a := by simp only [A, a, hw]
  change complexCurl (fun q => A q * G q) w = b * adjointExpression (realProfile G) x y
  rw [complexCurl_mul hA hG, hA0]
  unfold complexCurl
  rw [hX, hY, ← hGX, ← hGY, hAB]
  unfold adjointExpression realProfile
  change _ = b * (Complex.I * (y : ℂ) * partialX (fun u v => G (complexPoint u v)) x y -
    (y : ℂ) * partialY (fun u v => G (complexPoint u v)) x y + (3 / 4 : ℂ) * G w)
  ring

theorem complexCurl_eta_adjointPartner {G : ℂ → ℂ} {x y : ℝ} (hy : 0 < y)
    (hG : DifferentiableAt ℝ G (complexPoint x y)) :
    complexCurl (fun q => ModularForm.eta q * adjointPartner G q) (complexPoint x y) =
      ModularForm.eta (complexPoint x y) * ((y ^ (-(7 / 4 : ℝ)) : ℝ) : ℂ) *
        adjointExpression (realProfile G) x y := by
  let w := complexPoint x y
  have hw : 0 < w.im := by rw [show w.im = y from complexPoint_im x y]; exact hy
  have hEta := ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw
  have hHeight : DifferentiableAt ℝ (fun q : ℂ => ((q.im ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ)) w :=
    (Real.hasDerivAt_rpow_const (p := -(3 / 4 : ℝ)) (Or.inl hw.ne')).ofReal_comp.differentiableAt.comp
      w Complex.imCLM.differentiableAt
  have hPart : DifferentiableAt ℝ (adjointPartner G) w := hHeight.mul hG
  rw [complexCurl_mul (hEta.restrictScalars ℝ) hPart, complexCurl_holomorphic hEta,
    zero_mul, add_zero, complexCurl_adjointPartner hy hG, mul_assoc]

end
end ManuscriptAudit.Paper8MaassAdjointCurl

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassAdjointCurl.complexCurl_eta_adjointPartner
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
