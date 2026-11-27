import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.RealDeriv
import PrimalitySheafVerification.ManuscriptAudit.Paper8NegativeHalfMaassFactorization

/-! The zero raising equation is the actual Cauchy–Riemann equation for the coefficient. -/

namespace ManuscriptAudit.Paper8CuspRaisingHolomorphic

open MaassLaplacian Paper8NegativeHalfMaassFactorization

noncomputable section

private theorem real_derivative_complex_linear (H : ℂ → ℂ) {z : ℂ}
    (hH : DifferentiableAt ℝ H z)
    (hc : fderiv ℝ H z Complex.I = Complex.I * fderiv ℝ H z 1) :
    DifferentiableAt ℂ H z := by
  let L := fderiv ℝ H z
  let M : ℂ →L[ℂ] ℂ := (ContinuousLinearMap.id ℂ ℂ).smulRight (L 1)
  refine (differentiableAt_iff_restrictScalars ℝ hH).mpr ⟨M, ?_⟩
  apply ContinuousLinearMap.ext
  intro w
  change w * L 1 = L w
  have hw : (w.re : ℂ) + (w.im : ℂ)*Complex.I = w := Complex.re_add_im w
  rw [← hw, L.map_add]
  have h₁ : L (w.re : ℂ) = w.re • L 1 := by
    simpa only [Complex.real_smul, mul_one] using L.map_smul w.re (1 : ℂ)
  have h₂ : L ((w.im : ℂ)*Complex.I) = w.im • L Complex.I := by
    simpa only [Complex.real_smul] using L.map_smul w.im Complex.I
  rw [h₁,h₂, hc]
  simp only [Complex.real_smul]
  ring

def profile (H : ℂ → ℂ) (x y : ℝ) : ℂ :=
  ((y^(1/4 : ℝ) : ℝ) : ℂ) * star (H (complexPoint x y))

theorem raising_eq_zero_implies_complex_differentiable (H : ℂ → ℂ) (x y : ℝ) (hy : 0 < y)
    (hH : DifferentiableAt ℝ H (complexPoint x y)) (hz : raising (profile H) x y = 0) :
    DifferentiableAt ℂ H (complexPoint x y) := by
  let z := complexPoint x y
  let L := fderiv ℝ H z
  let W : ℝ → ℂ := fun t => ((t^(1/4 : ℝ) : ℝ) : ℂ)
  have hX : HasDerivAt (fun t => complexPoint t y) (1 : ℂ) x := by
    simpa only [complexPoint, id_eq, Complex.ofReal_one] using
      ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ)*Complex.I)
  have hY : HasDerivAt (fun t => complexPoint x t) Complex.I y := by
    simpa only [complexPoint, id_eq, Complex.ofReal_one, one_mul] using
      (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)
  have dX : HasDerivAt (fun t => H (complexPoint t y)) (L 1) x :=
    hH.hasFDerivAt.comp_hasDerivAt x hX
  have dY : HasDerivAt (fun t => H (complexPoint x t)) (L Complex.I) y :=
    hH.hasFDerivAt.comp_hasDerivAt y hY
  have cX : HasDerivAt (fun t => star (H (complexPoint t y))) (star (L 1)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt x dX
  have cY : HasDerivAt (fun t => star (H (complexPoint x t))) (star (L Complex.I)) y :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt y dY
  have dW : HasDerivAt W ((1/4 : ℂ)*((y^(1/4-1 : ℝ) : ℝ) : ℂ)) y := by
    simpa only [W, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
      using (Real.hasDerivAt_rpow_const (p := (1/4 : ℝ)) (Or.inl hy.ne')).ofReal_comp
  have hShift : (y : ℂ)*((y^(1/4-1 : ℝ) : ℝ) : ℂ) = W y := by
    have h := Real.rpow_add hy 1 (1/4-1)
    rw [show 1+(1/4-1 : ℝ) = 1/4 by ring, Real.rpow_one] at h
    simpa only [W, Complex.ofReal_mul] using congrArg Complex.ofReal h.symm
  have dxp : partialX (profile H) x y = W y * star (L 1) := (cX.const_mul (W y)).deriv
  have dyp : partialY (profile H) x y =
        (1/4 : ℂ)*((y^(1/4-1 : ℝ) : ℝ) : ℂ)*star (H z) +
        W y*star (L Complex.I) := (dW.mul cY).deriv
  rw [raising, dxp, dyp] at hz
  change Complex.I*(y : ℂ)*(W y*star (L 1)) +
    (y : ℂ)*((1/4 : ℂ)*((y^(1/4-1 : ℝ) : ℝ) : ℂ)*star (H z) +
      W y*star (L Complex.I)) - (1/4 : ℂ)*(W y*star (H z)) = 0 at hz
  have hProd : ((y : ℂ)*W y)*(Complex.I*star (L 1)+star (L Complex.I)) = 0 := by
    linear_combination hz - (1/4 : ℂ)*star (H z)*hShift
  have hW0 : W y ≠ 0 := by
    change (((y^(1/4 : ℝ) : ℝ) : ℂ)) ≠ 0
    exact_mod_cast (Real.rpow_pos_of_pos hy (1/4 : ℝ)).ne'
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hAdd := (mul_eq_zero.mp hProd).resolve_left (mul_ne_zero hy0 hW0)
  have hStar : star (L Complex.I) = -(Complex.I*star (L 1)) := by
    linear_combination hAdd
  apply real_derivative_complex_linear H hH
  have hR := congrArg star hStar
  simpa [star_mul, Complex.conj_I, mul_comm] using hR

end
end ManuscriptAudit.Paper8CuspRaisingHolomorphic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8CuspRaisingHolomorphic.raising_eq_zero_implies_complex_differentiable
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun d => !allowed.contains d
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
