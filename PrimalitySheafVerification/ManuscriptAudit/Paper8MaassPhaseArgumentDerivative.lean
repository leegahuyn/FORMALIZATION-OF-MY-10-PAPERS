import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic

/-! Directional logarithmic derivative of the inverse complex argument factor. -/

namespace ManuscriptAudit.Paper8MaassPhaseArgumentDerivative

noncomputable section

private theorem hasDerivAt_complex_affine (d e : ℂ) :
    HasDerivAt (fun t : ℝ => d + (t : ℂ) * e) e 0 := by
  simpa only [Complex.ofReal_one, one_mul, zero_add] using
    (hasDerivAt_const (0 : ℝ) d).add (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const e)

theorem hasDerivAt_complex_norm_affine {d : ℂ} (e : ℂ) (hd : d ≠ 0) :
    HasDerivAt (fun t : ℝ => ‖d + (t : ℂ) * e‖) (‖d‖ * (e / d).re) 0 := by
  let D (t : ℝ) := d + (t : ℂ) * e
  have hD₀ : D 0 = d := by simp [D]
  have hDn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hR : HasDerivAt (fun t : ℝ => d.re + t * e.re) e.re 0 := by
    simpa only [one_mul, zero_add] using
      (hasDerivAt_const (0 : ℝ) d.re).add ((hasDerivAt_id' (0 : ℝ)).mul_const e.re)
  have hI : HasDerivAt (fun t : ℝ => d.im + t * e.im) e.im 0 := by
    simpa only [one_mul, zero_add] using
      (hasDerivAt_const (0 : ℝ) d.im).add ((hasDerivAt_id' (0 : ℝ)).mul_const e.im)
  have hSq : HasDerivAt (fun t : ℝ => ‖D t‖ ^ 2)
      (2 * (d.re * e.re + d.im * e.im)) 0 := by
    convert (hR.pow 2).add (hI.pow 2) using 1
    · funext t
      unfold D
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, zero_add]
      ring
    · norm_num <;> ring
  have hN : HasDerivAt (fun t : ℝ => Real.sqrt (‖D t‖ ^ 2))
      ((2 * (d.re * e.re + d.im * e.im)) / (2 * Real.sqrt (‖D 0‖ ^ 2))) 0 :=
    hSq.sqrt (by rw [hD₀]; exact (sq_pos_of_pos hDn).ne')
  simp_rw [Real.sqrt_sq (norm_nonneg _)] at hN
  rw [hD₀] at hN
  have hVal : (2 * (d.re * e.re + d.im * e.im)) / (2 * ‖d‖) = ‖d‖ * (e / d).re := by
    rw [Complex.div_re, ← Complex.sq_norm]
    field_simp [hDn.ne'] <;> ring
  rw [hVal] at hN
  exact hN

theorem hasDerivAt_inverse_argument_affine {d : ℂ} (e : ℂ) (hd : d ≠ 0) :
    HasDerivAt (fun t : ℝ => ((‖d + (t : ℂ) * e‖ : ℝ) : ℂ) / (d + (t : ℂ) * e))
      (-Complex.I * ((e / d).im : ℂ) * ((‖d‖ : ℂ) / d)) 0 := by
  have hD := hasDerivAt_complex_affine d e
  have hN := (hasDerivAt_complex_norm_affine e hd).ofReal_comp
  have hQ := hN.div hD (by simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hd)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_mul] at hQ
  have hSwap : (((e / d).re : ℝ) : ℂ) - e / d = -Complex.I * ((e / d).im : ℂ) := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  have hEq : (((‖d‖ : ℂ) * ((e / d).re : ℂ)) * d - (‖d‖ : ℂ) * e) / d ^ 2 =
      -Complex.I * ((e / d).im : ℂ) * ((‖d‖ : ℂ) / d) := by
    calc
      _ = ((‖d‖ : ℂ) / d) * (((e / d).re : ℂ) - e / d) := by field_simp [hd] <;> ring
      _ = _ := by rw [hSwap]; ring
  rw [hEq] at hQ
  exact hQ

end
end ManuscriptAudit.Paper8MaassPhaseArgumentDerivative

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassPhaseArgumentDerivative.hasDerivAt_inverse_argument_affine
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
