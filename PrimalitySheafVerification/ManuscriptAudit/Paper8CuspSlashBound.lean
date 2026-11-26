import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-! The literal cusp-slash denominator is uniformly separated from zero on the stated circle. -/

namespace ManuscriptAudit.Paper8CuspSlashBound

open scoped MatrixGroups UpperHalfPlane

noncomputable section

def qValue (z : ℍ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ))

def slashDenominator (g : SL(2, ℤ)) (z : ℍ) : ℂ :=
  (g.val 1 0 : ℂ) * (z : ℂ) + (g.val 1 1 : ℂ)

theorem qValue_norm (z : ℍ) :
    ‖qValue z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [qValue, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem height_gt_one_twelfth (z : ℍ) (hradius : ‖qValue z‖ = 9 / 20) :
    1 / 12 < z.im := by
  by_contra! h
  have hPi : Real.pi < 3.15 := Real.pi_lt_d2
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * Real.pi by positivity)
  have he := Real.add_one_le_exp (-(2 * Real.pi * z.im))
  rw [qValue_norm] at hradius
  linarith

private theorem integer_abs_ge_one_as_real {n : ℤ} (hn : n ≠ 0) :
    (1 : ℝ) ≤ |(n : ℝ)| := by
  rcases lt_or_gt_of_ne hn with h | h
  · have h₁ : n ≤ -1 := by omega
    have h₂ : (n : ℝ) ≤ -1 := by exact_mod_cast h₁
    rw [abs_of_nonpos (by linarith : (n : ℝ) ≤ 0)]
    linarith
  · have h₁ : 1 ≤ n := by omega
    have h₂ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₁
    exact h₂.trans (le_abs_self _)

theorem slashDenominator_norm_ge_height_of_c_ne_zero (g : SL(2, ℤ)) (z : ℍ)
    (hc : g.val 1 0 ≠ 0) : z.im ≤ ‖slashDenominator g z‖ := by
  have him : (slashDenominator g z).im = (g.val 1 0 : ℝ) * z.im := by
    simp [slashDenominator, Complex.mul_im]
  calc
    z.im = 1 * z.im := (one_mul _).symm
    _ ≤ |(g.val 1 0 : ℝ)| * z.im :=
      mul_le_mul_of_nonneg_right (integer_abs_ge_one_as_real hc) z.im_pos.le
    _ = |(slashDenominator g z).im| := by
      rw [him, abs_mul, abs_of_pos z.im_pos]
    _ ≤ _ := Complex.abs_im_le_norm _

theorem slashDenominator_norm_ge_one_of_c_eq_zero (g : SL(2, ℤ)) (z : ℍ)
    (hc : g.val 1 0 = 0) : (1 : ℝ) ≤ ‖slashDenominator g z‖ := by
  have hd : g.val 1 1 ≠ 0 := by
    intro hd
    have hDet : Matrix.det g.val = 1 := g.property
    rw [Matrix.det_fin_two, hc, hd] at hDet
    simp only [mul_zero, sub_zero] at hDet
    exact Int.zero_ne_one hDet
  have hRe : (slashDenominator g z).re = (g.val 1 1 : ℝ) := by simp [slashDenominator, hc]
  calc
    1 ≤ |(g.val 1 1 : ℝ)| := integer_abs_ge_one_as_real hd
    _ = |(slashDenominator g z).re| := by rw [hRe]
    _ ≤ _ := Complex.abs_re_le_norm _


/-- The bound holds at every contour node for every valid modular representative. -/
theorem slashDenominator_norm_gt_one_twelfth (g : SL(2, ℤ)) (z : ℍ)
    (hradius : ‖qValue z‖ = 9 / 20) : 1 / 12 < ‖slashDenominator g z‖ := by
  by_cases hc : g.val 1 0 = 0
  · exact (by norm_num : (1 / 12 : ℝ) < 1).trans_le
      (slashDenominator_norm_ge_one_of_c_eq_zero g z hc)
  · exact (height_gt_one_twelfth z hradius).trans_le
      (slashDenominator_norm_ge_height_of_c_ne_zero g z hc)

end
end ManuscriptAudit.Paper8CuspSlashBound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8CuspSlashBound.qValue_norm,
      ``ManuscriptAudit.Paper8CuspSlashBound.height_gt_one_twelfth,
      ``ManuscriptAudit.Paper8CuspSlashBound.slashDenominator_norm_ge_height_of_c_ne_zero,
      ``ManuscriptAudit.Paper8CuspSlashBound.slashDenominator_norm_ge_one_of_c_eq_zero,
      ``ManuscriptAudit.Paper8CuspSlashBound.slashDenominator_norm_gt_one_twelfth] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
