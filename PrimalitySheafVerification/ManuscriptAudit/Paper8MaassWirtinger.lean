import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaSquaredModularity

/-! The real-derivative projection used by the Maass raising operator and its holomorphic chain rule. -/

namespace ManuscriptAudit.Paper8MaassWirtinger

open UpperHalfPlane MaassLaplacian
open Paper8ActualEtaSquaredModularity
open scoped MatrixGroups

noncomputable section

def derivativeZ (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ F z 1 - Complex.I * fderiv ℝ F z Complex.I) / 2

private theorem complex_projection_scale (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v - Complex.I * L (Complex.I * v) = v * (L 1 - Complex.I * L Complex.I) := by
  have hv : v.re • (1 : ℂ) + v.im • Complex.I = v := by
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im v
  have hi : (-v.im) • (1 : ℂ) + v.re • Complex.I = Complex.I * v := by
    apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
  have hL : L v = v.re • L 1 + v.im • L Complex.I := by
    calc
      _ = L (v.re • (1 : ℂ) + v.im • Complex.I) := congrArg L hv.symm
      _ = _ := by rw [map_add, map_smul, map_smul]
  have hI : L (Complex.I * v) = (-v.im) • L 1 + v.re • L Complex.I := by
    calc
      _ = L ((-v.im) • (1 : ℂ) + v.re • Complex.I) := congrArg L hi.symm
      _ = _ := by rw [map_add, map_smul, map_smul]
  rw [hL, hI]
  calc
    _ = (v.re • (1 : ℂ) + v.im • Complex.I) * (L 1 - Complex.I * L Complex.I) := by
      simp only [Complex.real_smul, Complex.ofReal_neg]
      linear_combination ((v.im : ℂ) * L Complex.I) * Complex.I_sq
    _ = _ := by rw [hv]

theorem derivativeZ_comp_holomorphic {F f : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F (f z)) (hf : DifferentiableAt ℂ f z) :
    derivativeZ (F ∘ f) z = deriv f z * derivativeZ F (f z) := by
  let L := fderiv ℝ F (f z)
  let d := deriv f z
  have h := hF.hasFDerivAt.comp z hf.hasDerivAt.complexToReal_fderiv
  unfold derivativeZ
  rw [h.fderiv]
  change (L (d * 1) - Complex.I * L (d * Complex.I)) / 2 =
    d * ((L 1 - Complex.I * L Complex.I) / 2)
  rw [mul_one, mul_comm d Complex.I, complex_projection_scale]
  ring

theorem derivativeZ_const_mul {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (c : ℂ) :
    derivativeZ (fun w => c * F w) z = c * derivativeZ F z := by
  have h := (hF.hasFDerivAt.const_smul c).fderiv
  change fderiv ℝ (fun w => c * F w) z = c • fderiv ℝ F z at h
  unfold derivativeZ
  rw [h]
  change (c * fderiv ℝ F z 1 - Complex.I * (c * fderiv ℝ F z Complex.I)) / 2 =
    c * ((fderiv ℝ F z 1 - Complex.I * fderiv ℝ F z Complex.I) / 2)
  ring

theorem derivativeZ_eq_partials {F : ℂ → ℂ} {x y : ℝ}
    (hF : DifferentiableAt ℝ F (complexPoint x y)) :
    derivativeZ F (complexPoint x y) =
      (partialX (fun u v => F (complexPoint u v)) x y -
        Complex.I * partialY (fun u v => F (complexPoint u v)) x y) / 2 := by
  have hX : HasDerivAt (fun t => complexPoint t y) (1 : ℂ) x := by
    simpa only [id_eq] using horizontal_derivative (hasDerivAt_id (complexPoint x y))
  have hY : HasDerivAt (fun t => complexPoint x t) Complex.I y := by
    simpa only [id_eq, mul_one] using vertical_derivative (hasDerivAt_id (complexPoint x y))
  have hDx : partialX (fun u v => F (complexPoint u v)) x y =
      fderiv ℝ F (complexPoint x y) 1 :=
    (hF.hasFDerivAt.comp_hasDerivAt x hX).deriv
  have hDy : partialY (fun u v => F (complexPoint u v)) x y =
      fderiv ℝ F (complexPoint x y) Complex.I :=
    (hF.hasFDerivAt.comp_hasDerivAt y hY).deriv
  rw [hDx, hDy, derivativeZ]

theorem fractionalLinear_hasDerivAt (g : SL(2, ℤ)) (z : ℍ) :
    HasDerivAt (fractionalLinear g) ((denominator g z ^ 2)⁻¹) z := by
  have hNum : HasDerivAt (fun w : ℂ => (g 0 0 : ℂ) * w + (g 0 1 : ℂ))
      (g 0 0 : ℂ) z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (z : ℂ)).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)
  have hDen : HasDerivAt (denominator g) (g 1 0 : ℂ) z := by
    simpa only [denominator, id_eq, mul_one] using
      ((hasDerivAt_id (z : ℂ)).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)
  have h := hNum.div hDen (denominator_ne_zero g z)
  have hDInt : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have hD := g.2
    change Matrix.det g.1 = (1 : ℤ) at hD
    rwa [Matrix.det_fin_two] at hD
  have hD : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast hDInt
  change HasDerivAt (fractionalLinear g)
    (((g 0 0 : ℂ) * denominator g z -
      ((g 0 0 : ℂ) * (z : ℂ) + (g 0 1 : ℂ)) * (g 1 0 : ℂ)) / denominator g z ^ 2) z at h
  have hOne : (g 0 0 : ℂ) * denominator g z -
      ((g 0 0 : ℂ) * (z : ℂ) + (g 0 1 : ℂ)) * (g 1 0 : ℂ) = 1 := by
    unfold denominator
    linear_combination hD
  rw [hOne, one_div] at h
  exact h

end
end ManuscriptAudit.Paper8MaassWirtinger

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassWirtinger.derivativeZ_comp_holomorphic,
      ``ManuscriptAudit.Paper8MaassWirtinger.derivativeZ_const_mul,
      ``ManuscriptAudit.Paper8MaassWirtinger.derivativeZ_eq_partials,
      ``ManuscriptAudit.Paper8MaassWirtinger.fractionalLinear_hasDerivAt] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
