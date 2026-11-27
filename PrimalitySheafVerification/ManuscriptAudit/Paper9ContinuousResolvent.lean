import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A nonsingular denominator for the continuous spectral resolvent

For spectral value 1/4+t² and parameter s(1-s), their difference
is t²+(s-1/2)². Its actual reciprocal is uniformly bounded for Re(s)>1.
This is an elementary comparison with the denominator printed on p. 425.
-/

namespace ManuscriptAudit.Paper9ContinuousResolvent

noncomputable section

def denominator (s : ℂ) (t : ℝ) : ℂ :=
  1 / 4 + (t : ℂ) ^ 2 - s * (1 - s)

theorem denominator_factor (s : ℂ) (t : ℝ) :
    denominator s t =
      (s - 1 / 2 - (t : ℂ) * Complex.I) * (s - 1 / 2 + (t : ℂ) * Complex.I) := by
  unfold denominator
  calc
    _ = (s - 1 / 2) ^ 2 + (t : ℂ) ^ 2 := by ring
    _ = (s - 1 / 2) ^ 2 - (t : ℂ) ^ 2 * Complex.I ^ 2 := by rw [Complex.I_sq]; ring
    _ = _ := by ring

theorem denominator_norm_lower {s : ℂ} (hs : 1 < s.re) (t : ℝ) :
    (s.re - 1 / 2) ^ 2 ≤ ‖denominator s t‖ := by
  have hPos : 0 < s.re - 1 / 2 := by linarith
  have hHalf : (1 / 2 : ℂ).re = 1 / 2 := by
    change (((1 : ℝ) : ℂ) / ((2 : ℝ) : ℂ)).re = _
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  have hImag : ((t : ℂ) * Complex.I).re = 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero]
  have hMinus : s.re - 1 / 2 ≤ ‖s - 1 / 2 - (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm (s - 1 / 2 - (t : ℂ) * Complex.I)
    simpa only [Complex.sub_re, hHalf, hImag, sub_zero, abs_of_pos hPos] using h
  have hPlus : s.re - 1 / 2 ≤ ‖s - 1 / 2 + (t : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm (s - 1 / 2 + (t : ℂ) * Complex.I)
    simpa only [Complex.sub_re, Complex.add_re, hHalf, hImag, add_zero, abs_of_pos hPos] using h
  rw [denominator_factor, norm_mul, pow_two]
  exact mul_le_mul hMinus hPlus hPos.le (norm_nonneg _)

theorem denominator_ne_zero {s : ℂ} (hs : 1 < s.re) (t : ℝ) : denominator s t ≠ 0 := by
  have hPos : 0 < s.re - 1 / 2 := by linarith
  exact norm_pos_iff.mp ((pow_pos hPos 2).trans_le (denominator_norm_lower hs t))

theorem reciprocal_norm_le_four {s : ℂ} (hs : 1 < s.re) (t : ℝ) :
    ‖(denominator s t)⁻¹‖ ≤ 4 := by
  have h : (1 / 4 : ℝ) ≤ ‖denominator s t‖ := by
    have hp : (1 / 2 : ℝ) ≤ s.re - 1 / 2 := by linarith
    have hPow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hp 2
    have hQuarter : (1 / 4 : ℝ) ≤ (s.re - 1 / 2) ^ 2 := by norm_num at hPow ⊢; exact hPow
    exact hQuarter.trans (denominator_norm_lower hs t)
  rw [norm_inv, ← one_div]
  calc
    _ ≤ 1 / (1 / 4 : ℝ) := one_div_le_one_div_of_le (by norm_num) h
    _ = _ := by norm_num

end
end ManuscriptAudit.Paper9ContinuousResolvent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9ContinuousResolvent.denominator_factor,
      ``ManuscriptAudit.Paper9ContinuousResolvent.denominator_norm_lower,
      ``ManuscriptAudit.Paper9ContinuousResolvent.denominator_ne_zero,
      ``ManuscriptAudit.Paper9ContinuousResolvent.reciprocal_norm_le_four] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
