import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The actual Jacobi theta norm separates imaginary height from its unit translate. -/

namespace ManuscriptAudit.Paper9ThetaUnitTranslate

noncomputable section

def term (τ : ℂ) (n : ℕ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) ^ 2 * τ)

def axis (y : ℝ) : ℂ := (y : ℂ) * Complex.I

def positiveTerm (y : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * y)

private theorem axis_im (y : ℝ) : (axis y).im = y := by simp [axis, Complex.mul_im]

private theorem term_axis (y : ℝ) (n : ℕ) : term (axis y) n = (positiveTerm y n : ℂ) := by
  rw [term, positiveTerm, Complex.ofReal_exp]
  congr 1
  unfold axis
  push_cast
  calc
    _ = (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (y : ℂ) * Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

private theorem term_norm (τ : ℂ) (n : ℕ) :
    ‖term τ n‖ = Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * τ.im) := by
  have h : (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) ^ 2 * τ =
      ((Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) * τ * Complex.I := by
    push_cast
    ring
  rw [term, h, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero, mul_one]
  ring

private theorem translated_term_norm (y : ℝ) (n : ℕ) :
    ‖term (axis y + 1) n‖ = positiveTerm y n := by
  rw [term_norm, positiveTerm]
  simp only [Complex.add_im, Complex.one_im, add_zero, axis_im]

private theorem translated_first_term (y : ℝ) :
    term (axis y + 1) 0 = -(positiveTerm y 0 : ℂ) := by
  have h : term (axis y + 1) 0 = term (axis y) 0 * Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    simp only [term, Nat.cast_zero, zero_add, one_pow, mul_one, mul_add, Complex.exp_add]
  rw [h, Complex.exp_pi_mul_I, term_axis, mul_neg_one]

theorem translated_theta_norm_strictly_smaller {y : ℝ} (hy : 0 < y) :
    ‖jacobiTheta (axis y + 1)‖ < ‖jacobiTheta (axis y)‖ := by
  have hAxis : 0 < (axis y).im := by simpa only [axis_im] using hy
  have hShift : 0 < (axis y + 1).im := by
    simpa only [Complex.add_im, Complex.one_im, add_zero, axis_im] using hy
  have hA : HasSum (term (axis y)) ((jacobiTheta (axis y) - 1) / 2) :=
    hasSum_nat_jacobiTheta hAxis
  have hB : Summable (term (axis y + 1)) := (hasSum_nat_jacobiTheta hShift).summable
  have hP : Summable (positiveTerm y) :=
    (Complex.reCLM.hasSum hA).summable.congr fun n => by
      change (term (axis y) n).re = positiveTerm y n
      rw [term_axis, Complex.ofReal_re]
  have hCast : (∑' n : ℕ, term (axis y) n) = ((∑' n : ℕ, positiveTerm y n : ℝ) : ℂ) := by
    refine ((Complex.ofRealCLM.hasSum hP.hasSum).congr_fun (fun n => ?_)).tsum_eq
    simpa only [Complex.ofRealCLM_apply] using term_axis y n
  let A : ℝ := positiveTerm y 0
  let R : ℝ := ∑' n : ℕ, positiveTerm y (n + 1)
  have hPos : 0 < A := Real.exp_pos _
  have hR : 0 ≤ R := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hStd : ‖jacobiTheta (axis y)‖ = 1 + 2 * A + 2 * R := by
    have hEq : jacobiTheta (axis y) = ((1 + 2 * A + 2 * R : ℝ) : ℂ) := by
      rw [jacobiTheta_eq_tsum_nat hAxis]
      change 1 + 2 * (∑' n : ℕ, term (axis y) n) = _
      rw [hCast, hP.tsum_eq_zero_add]
      change 1 + 2 * ((A + R : ℝ) : ℂ) = _
      push_cast
      ring
    rw [hEq, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hAbs : Summable (fun n : ℕ => ‖term (axis y + 1) (n + 1)‖) := by
    exact ((summable_nat_add_iff 1).2 hP).congr fun n => (translated_term_norm y (n + 1)).symm
  have hTail : ‖∑' n : ℕ, term (axis y + 1) (n + 1)‖ ≤ R := by
    have h := norm_tsum_le_tsum_norm hAbs
    simpa only [translated_term_norm, R] using h
  have hSplit : jacobiTheta (axis y + 1) =
      ((1 - 2 * A : ℝ) : ℂ) + 2 * (∑' n : ℕ, term (axis y + 1) (n + 1)) := by
    rw [jacobiTheta_eq_tsum_nat hShift]
    change 1 + 2 * (∑' n : ℕ, term (axis y + 1) n) = _
    rw [hB.tsum_eq_zero_add, translated_first_term]
    change 1 + 2 * (-(A : ℂ) + (∑' n : ℕ, term (axis y + 1) (n + 1))) = _
    push_cast
    ring
  rw [hSplit, hStd]
  calc
    _ ≤ ‖((1 - 2 * A : ℝ) : ℂ)‖ + ‖(2 : ℂ) * (∑' n : ℕ, term (axis y + 1) (n + 1))‖ :=
      norm_add_le _ _
    _ = |1 - 2 * A| + 2 * ‖∑' n : ℕ, term (axis y + 1) (n + 1)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hTwo]
    _ ≤ |1 - 2 * A| + 2 * R :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hTail (by norm_num : (0 : ℝ) ≤ 2))
    _ < _ := by
      have h₀ : |1 - 2 * A| < 1 + 2 * A := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith

end
end ManuscriptAudit.Paper9ThetaUnitTranslate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9ThetaUnitTranslate.translated_theta_norm_strictly_smaller
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms name
  let bad := axioms.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {axioms}"
