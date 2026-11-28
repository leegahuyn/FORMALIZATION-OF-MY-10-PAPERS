import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassWirtinger

/-! Real curl product and holomorphic pullback calculus for the Green current. -/

namespace ManuscriptAudit.Paper8MaassCurlCalculus

open Function Paper8MaassWirtinger

noncomputable section

def complexCurl (J : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * fderiv ℝ J z 1 - fderiv ℝ J z Complex.I

theorem complexCurl_mul {U V : ℂ → ℂ} {z : ℂ}
    (hU : DifferentiableAt ℝ U z) (hV : DifferentiableAt ℝ V z) :
    complexCurl (fun w => U w * V w) z =
      U z * complexCurl V z + complexCurl U z * V z := by
  have h : fderiv ℝ (fun w => U w * V w) z =
      U z • fderiv ℝ V z + V z • fderiv ℝ U z := by
    change fderiv ℝ (U * V) z = _
    exact fderiv_mul hU hV
  unfold complexCurl
  rw [h]
  change Complex.I * (U z * fderiv ℝ V z 1 + V z * fderiv ℝ U z 1) -
    (U z * fderiv ℝ V z Complex.I + V z * fderiv ℝ U z Complex.I) = _
  ring

private theorem conjugate_projection_scale (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    Complex.I * L v - L (Complex.I * v) =
      (starRingEnd ℂ) v * (Complex.I * L 1 - L Complex.I) := by
  have hv : v.re • (1 : ℂ) + v.im • Complex.I = v := by
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im v
  have hi : (-v.im) • (1 : ℂ) + v.re • Complex.I = Complex.I * v := by
    apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
  have hconj : (starRingEnd ℂ) v = (v.re : ℂ) - (v.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hL : L v = v.re • L 1 + v.im • L Complex.I := by
    calc
      _ = L (v.re • (1 : ℂ) + v.im • Complex.I) := congrArg L hv.symm
      _ = _ := by rw [map_add, map_smul, map_smul]
  have hI : L (Complex.I * v) = (-v.im) • L 1 + v.re • L Complex.I := by
    calc
      _ = L ((-v.im) • (1 : ℂ) + v.re • Complex.I) := congrArg L hi.symm
      _ = _ := by rw [map_add, map_smul, map_smul]
  rw [hL, hI, hconj]
  simp only [Complex.real_smul, Complex.ofReal_neg]
  linear_combination ((v.im : ℂ) * L 1) * Complex.I_sq

theorem complexCurl_comp_holomorphic {J f : ℂ → ℂ} {z : ℂ}
    (hJ : DifferentiableAt ℝ J (f z)) (hf : DifferentiableAt ℂ f z) :
    complexCurl (J ∘ f) z = (starRingEnd ℂ) (deriv f z) * complexCurl J (f z) := by
  let L := fderiv ℝ J (f z)
  let d := deriv f z
  have h := hJ.hasFDerivAt.comp z hf.hasDerivAt.complexToReal_fderiv
  unfold complexCurl
  rw [h.fderiv]
  change Complex.I * L (d * 1) - L (d * Complex.I) =
    (starRingEnd ℂ) d * (Complex.I * L 1 - L Complex.I)
  rw [mul_one, mul_comm d Complex.I, conjugate_projection_scale]

theorem complexCurl_holomorphic {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    complexCurl f z = 0 := by
  unfold complexCurl
  rw [hf.hasDerivAt.complexToReal_fderiv.fderiv]
  change Complex.I * (deriv f z * 1) - deriv f z * Complex.I = 0
  ring

theorem complexCurl_pullback_holomorphic {J f a : ℂ → ℂ} {z : ℂ}
    (hJ : DifferentiableAt ℝ J (f z)) (hf : DifferentiableAt ℂ f z)
    (ha : DifferentiableAt ℂ a z) :
    complexCurl (fun w => J (f w) * a w) z =
      a z * (starRingEnd ℂ) (deriv f z) * complexCurl J (f z) := by
  have hComp : DifferentiableAt ℝ (J ∘ f) z := hJ.comp z (hf.restrictScalars ℝ)
  change complexCurl (fun w => (J ∘ f) w * a w) z = _
  rw [complexCurl_mul hComp (ha.restrictScalars ℝ), complexCurl_holomorphic ha,
    complexCurl_comp_holomorphic hJ hf, mul_zero, zero_add]
  ring

theorem complexCurl_ofReal {g : ℂ → ℝ} {z : ℂ} (hg : DifferentiableAt ℝ g z) :
    complexCurl (fun w => (g w : ℂ)) z =
      2 * Complex.I * (starRingEnd ℂ) (derivativeZ (fun w => (g w : ℂ)) z) := by
  have h : fderiv ℝ (fun w => (g w : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ g z) :=
    (Complex.ofRealCLM.hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  unfold complexCurl derivativeZ
  rw [h]
  change Complex.I * ((fderiv ℝ g z 1 : ℝ) : ℂ) - ((fderiv ℝ g z Complex.I : ℝ) : ℂ) =
    2 * Complex.I * (starRingEnd ℂ)
      ((((fderiv ℝ g z 1 : ℝ) : ℂ) - Complex.I * ((fderiv ℝ g z Complex.I : ℝ) : ℂ)) / 2)
  simp only [map_div₀, map_sub, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  linear_combination -((fderiv ℝ g z Complex.I : ℝ) : ℂ) * Complex.I_sq

end
end ManuscriptAudit.Paper8MaassCurlCalculus

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassCurlCalculus.complexCurl_mul,
      ``ManuscriptAudit.Paper8MaassCurlCalculus.complexCurl_comp_holomorphic,
      ``ManuscriptAudit.Paper8MaassCurlCalculus.complexCurl_pullback_holomorphic,
      ``ManuscriptAudit.Paper8MaassCurlCalculus.complexCurl_ofReal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
