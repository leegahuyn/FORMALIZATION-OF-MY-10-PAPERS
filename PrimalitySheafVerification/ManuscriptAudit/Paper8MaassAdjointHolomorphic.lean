import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCriticalHolomorphic
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaSquaredModularity

/-! The critical Maass adjoint kernel becomes holomorphic after the exact inverse three-quarter height factor. -/

namespace ManuscriptAudit.Paper8MaassAdjointHolomorphic

open MaassLaplacian Paper8MaassCriticalHolomorphic Paper8NegativeHalfMaassFactorization

noncomputable section

def adjointPartner (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z.im ^ (-(3 / 4 : ℝ)) : ℝ) * G z

private theorem height_derivative {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => ((t ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ))
      ((-(3 / 4 : ℂ)) * ((y ^ (-(3 / 4 : ℝ) - 1) : ℝ) : ℂ)) y := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    using (Real.hasDerivAt_rpow_const (p := -(3 / 4 : ℝ)) (Or.inl hy.ne')).ofReal_comp

private theorem height_shift {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * ((y ^ (-(3 / 4 : ℝ) - 1) : ℝ) : ℂ) =
      ((y ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) := by
  have h := Real.rpow_add hy 1 (-(3 / 4 : ℝ) - 1)
  rw [show (1 : ℝ) + (-(3 / 4 : ℝ) - 1) = -(3 / 4 : ℝ) by ring, Real.rpow_one] at h
  simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal h.symm

theorem adjointPartner_differentiableAt {G : ℂ → ℂ} {x y : ℝ} (hy : 0 < y)
    (hG : DifferentiableAt ℝ G (complexPoint x y))
    (hAdj : adjointExpression (realProfile G) x y = 0) :
    DifferentiableAt ℂ (adjointPartner G) (complexPoint x y) := by
  let A : ℂ := (y ^ (-(3 / 4 : ℝ)) : ℝ)
  let B : ℂ := (y ^ (-(3 / 4 : ℝ) - 1) : ℝ)
  have hPow : DifferentiableAt ℝ
      (fun w : ℂ => ((w.im ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ)) (complexPoint x y) := by
    have hI : DifferentiableAt ℝ (fun w : ℂ => w.im) (complexPoint x y) :=
      Complex.imCLM.differentiableAt
    have hH : DifferentiableAt ℝ (fun t : ℝ => ((t ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ))
        (complexPoint x y).im := by
      simpa only [complexPoint_im] using (height_derivative hy).differentiableAt
    exact hH.comp _ hI
  have hReal : DifferentiableAt ℝ (adjointPartner G) (complexPoint x y) := hPow.mul hG
  apply differentiableAt_complex_of_coordinates hReal
  have hDx : partialX (realProfile (adjointPartner G)) x y =
      A * partialX (realProfile G) x y := by
    simpa only [realProfile, adjointPartner, complexPoint_im, partialX, A] using
      ((profile_horizontal hG).const_mul A).deriv
  have hDy : partialY (realProfile (adjointPartner G)) x y =
      (-(3 / 4 : ℂ)) * B * realProfile G x y + A * partialY (realProfile G) x y := by
    have hFun : realProfile (adjointPartner G) x =
        (fun t : ℝ => ((t ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ)) * realProfile G x := by
      funext t
      simp only [realProfile, adjointPartner, complexPoint_im, Pi.mul_apply]
    rw [partialY, hFun]
    exact ((height_derivative hy).mul (profile_vertical hG)).deriv
  have hShift : (y : ℂ) * B = A := height_shift hy
  rw [hDy, hDx]
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hy.ne')
  unfold adjointExpression at hAdj
  linear_combination -A * hAdj - ((3 / 4 : ℂ) * realProfile G x y) * hShift

theorem adjointGaugeProduct_differentiableOn {G : ℂ → ℂ}
    (hG : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ G z)
    (hAdj : ∀ x y : ℝ, 0 < y → adjointExpression (realProfile G) x y = 0) :
    DifferentiableOn ℂ (fun z => ModularForm.eta z * adjointPartner G z) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hPoint : complexPoint z.re z.im = z := Complex.re_add_im z
  have hReal : DifferentiableAt ℝ G (complexPoint z.re z.im) := by rw [hPoint]; exact hG z hz
  have hHol := adjointPartner_differentiableAt hz hReal (hAdj z.re z.im hz)
  rw [hPoint] at hHol
  exact ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).mul hHol).differentiableWithinAt

end
end ManuscriptAudit.Paper8MaassAdjointHolomorphic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassAdjointHolomorphic.adjointGaugeProduct_differentiableOn
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
