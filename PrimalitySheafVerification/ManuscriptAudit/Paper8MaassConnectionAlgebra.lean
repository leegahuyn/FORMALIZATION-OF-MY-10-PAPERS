import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-! Exact cancellation of the hyperbolic connection correction and invariance under frame rotation. -/

namespace ManuscriptAudit.Paper8MaassConnectionAlgebra

noncomputable section

theorem hyperbolic_connection_correction_cancel {d v : ℂ} {c y : ℝ}
    (hd : d ≠ 0) (hy : y ≠ 0) (hIm : d.im = c * y) :
    (((c : ℂ) * v / d).im) / 2 + v.re / (4 * y) -
      ((((starRingEnd ℂ) d / d) * v).re) / (4 * y) = 0 := by
  have hD : d - (starRingEnd ℂ) d = 2 * Complex.I * ((c * y : ℝ) : ℂ) := by
    apply Complex.ext
    · norm_num [Complex.sub_re, Complex.conj_re, Complex.mul_re, Complex.mul_im]
    · norm_num [Complex.sub_im, Complex.conj_im, Complex.mul_re, Complex.mul_im, hIm] <;> ring
  have hEq : v - ((starRingEnd ℂ) d / d) * v =
      (2 * Complex.I * ((c * y : ℝ) : ℂ)) * (v / d) := by
    field_simp [hd]
    linear_combination v * hD
  have hRe := congrArg Complex.re hEq
  have hR : ((2 * Complex.I * ((c * y : ℝ) : ℂ)) * (v / d)).re =
      -(2 * c * y * (v / d).im) := by
    norm_num [Complex.mul_re, Complex.mul_im] <;> ring
  change v.re - (((starRingEnd ℂ) d / d) * v).re = _ at hRe
  rw [hR] at hRe
  have hC : (((c : ℂ) * v / d).im) = c * (v / d).im := by
    rw [mul_div_assoc]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [hC]
  field_simp [hy]
  linarith only [hRe]

private theorem complex_norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem realLinear_complex_components (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z = (z.re : ℂ) * A 1 + (z.im : ℂ) * A Complex.I := by
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im z
  calc
    A z = A (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg A hz.symm
    _ = _ := by rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem realLinear_complex_unitRotation_energy (A : ℂ →L[ℝ] ℂ) {r : ℂ} (hr : ‖r‖ = 1) :
    ‖A r‖ ^ 2 + ‖A (Complex.I * r)‖ ^ 2 = ‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2 := by
  have hUnit : r.re ^ 2 + r.im ^ 2 = 1 := by rw [← complex_norm_sq, hr, one_pow]
  calc
    _ = (r.re ^ 2 + r.im ^ 2) * (‖A 1‖ ^ 2 + ‖A Complex.I‖ ^ 2) := by
      rw [realLinear_complex_components A r, realLinear_complex_components A (Complex.I * r)]
      simp only [complex_norm_sq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    _ = _ := by rw [hUnit, one_mul]

end
end ManuscriptAudit.Paper8MaassConnectionAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassConnectionAlgebra.hyperbolic_connection_correction_cancel,
      ``ManuscriptAudit.Paper8MaassConnectionAlgebra.realLinear_complex_unitRotation_energy] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
