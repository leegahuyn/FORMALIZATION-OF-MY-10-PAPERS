import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareKernel

/-! Exact height of an actual scaled row and a uniform bound on its integer translates. -/

namespace ManuscriptAudit.Paper8OddCrossPoincareHeight

open Matrix UpperHalfPlane MaassLaplacian Paper8OddCrossCuspNormalization
open Paper8OddCrossScaledRows Paper8OddCrossPoincareKernel
open scoped MatrixGroups

noncomputable section

def crossRowShift {D : ℕ} (A : CrossRow D) : ℝ :=
  scaledCrossMatrix A 1 1 / scaledCrossMatrix A 1 0

def translatePoint (n : ℤ) (z : ℍ) : ℍ :=
  ⟨complexPoint ((n : ℝ) + z.re) z.im, by simpa only [complexPoint_im] using z.im_pos⟩

theorem crossRowShift_mem {D : ℕ} (hD : 0 < D) (A : CrossRow D) :
    crossRowShift A ∈ Set.Ico (0 : ℝ) 1 := by
  have hD0 : 0 < (D : ℝ) := by exact_mod_cast hD
  have hLo : 0 ≤ (A.matrix 1 1 : ℝ) := by exact_mod_cast A.bottomNonneg
  have hHi : (A.matrix 1 1 : ℝ) < 4 * (D : ℝ) := by exact_mod_cast A.bottomBound
  have hc : 0 < 2 * (D : ℝ) := by positivity
  unfold crossRowShift
  rw [scaledCrossMatrix_lowerLeft]
  change 0 ≤ (A.matrix 1 1 : ℝ) / 2 / (2 * (D : ℝ)) ∧
    (A.matrix 1 1 : ℝ) / 2 / (2 * (D : ℝ)) < 1
  exact ⟨by positivity, (div_lt_iff₀ hc).2 (by linarith)⟩

theorem matrixMoebius_im (g : SL(2, ℝ)) (z : ℍ) (hc : g 1 0 ≠ 0) :
    (g • z).im = z.im /
      (g 1 0 ^ 2 * ((z.re + g 1 1 / g 1 0) ^ 2 + z.im ^ 2)) := by
  have hDet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe g
  have hAct : ((g • z : ℍ) : ℂ) = matrixMoebius g z := by
    simpa [matrixMoebius] using UpperHalfPlane.coe_specialLinearGroup_apply g z
  have hNorm : Complex.normSq ((g 1 0 : ℂ) * (z : ℂ) + (g 1 1 : ℂ)) =
      g 1 0 ^ 2 * ((z.re + g 1 1 / g 1 0) ^ 2 + z.im ^ 2) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    field_simp [hc] <;> ring
  change ((g • z : ℍ) : ℂ).im = _
  rw [hAct, matrixMoebius, Complex.div_im, hNorm]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.add_re, Complex.mul_re, sub_zero, ← sub_div,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  congr 1
  linear_combination z.im * hDet

theorem scaledCross_translate_height {D : ℕ} (hD : 0 < D) (A : CrossRow D) (z : ℍ) (n : ℤ) :
    (scaledCrossMatrix A • translatePoint n z).im =
      z.im / ((2 * (D : ℝ)) ^ 2 * ((((n : ℝ) + z.re) + crossRowShift A) ^ 2 + z.im ^ 2)) := by
  have hc : scaledCrossMatrix A 1 0 ≠ 0 := by
    rw [scaledCrossMatrix_lowerLeft]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hD.ne')
  rw [matrixMoebius_im _ _ hc]
  have hRe : (translatePoint n z).re = (n : ℝ) + z.re := by
    change (complexPoint ((n : ℝ) + z.re) z.im).re = _
    simp [complexPoint, Complex.add_re, Complex.mul_re]
  have hIm : (translatePoint n z).im = z.im := complexPoint_im _ _
  rw [hRe, hIm, ← crossRowShift, scaledCrossMatrix_lowerLeft]

def crossHeightConstant (z : ℍ) : ℝ := 2 + 2 * (|z.re| + 2) ^ 2 / z.im ^ 2

theorem crossHeightConstant_pos (z : ℍ) : 0 < crossHeightConstant z := by
  unfold crossHeightConstant
  positivity

private theorem translated_quad_le (x y a : ℝ) (hy : 0 < y)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℤ) :
    (|(n : ℝ)| + 1) ^ 2 ≤ (2 + 2 * (|x| + 2) ^ 2 / y ^ 2) *
      ((((n : ℝ) + x) + a) ^ 2 + y ^ 2) := by
  let u : ℝ := (n : ℝ) + x + a
  let B : ℝ := |x| + 2
  let K : ℝ := 2 + 2 * B ^ 2 / y ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 2 ≤ K := by
    dsimp only [K]
    exact le_add_of_nonneg_right (by positivity)
  have hTriangle : |(n : ℝ)| ≤ |u| + (|x| + a) := by
    have h1 := abs_add_le u (-(x + a))
    rw [← sub_eq_add_neg, abs_neg,
      show u - (x + a) = n by dsimp only [u]; ring] at h1
    have h2 := abs_add_le x a
    rw [abs_of_nonneg ha0] at h2
    linarith
  have hSq : (|(n : ℝ)| + 1) ^ 2 ≤ (|u| + B) ^ 2 := by
    have hLe : |(n : ℝ)| + 1 ≤ |u| + B := by
      linarith [show B = |x| + 2 from rfl]
    have hSum : 0 ≤ (|u| + B) + (|(n : ℝ)| + 1) :=
      add_nonneg (add_nonneg (abs_nonneg _) hB) (by positivity)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hLe) hSum]
  have hSquare : (|u| + B) ^ 2 ≤ 2 * u ^ 2 + 2 * B ^ 2 := by
    nlinarith [sq_nonneg (|u| - B), sq_abs u]
  have hY : K * y ^ 2 = 2 * y ^ 2 + 2 * B ^ 2 := by
    dsimp only [K]
    field_simp [hy.ne'] <;> ring
  calc
    _ ≤ (|u| + B) ^ 2 := hSq
    _ ≤ 2 * u ^ 2 + 2 * B ^ 2 := hSquare
    _ ≤ K * (u ^ 2 + y ^ 2) := by
      rw [mul_add, hY]
      linarith [mul_le_mul_of_nonneg_right hK (sq_nonneg u), sq_nonneg y]

theorem scaledCross_translate_height_le {D : ℕ} (hD : 0 < D) (A : CrossRow D) (z : ℍ) (n : ℤ) :
    (scaledCrossMatrix A • translatePoint n z).im ≤
      z.im * crossHeightConstant z / ((2 * (D : ℝ)) ^ 2 * (|(n : ℝ)| + 1) ^ 2) := by
  have hD0 : 0 < (D : ℝ) := by exact_mod_cast hD
  have h0 := (crossRowShift_mem hD A).1
  have h1 := (crossRowShift_mem hD A).2.le
  have hQuad := translated_quad_le z.re z.im (crossRowShift A) z.im_pos h0 h1 n
  rw [scaledCross_translate_height hD]
  apply (div_le_div_iff₀ (by have := z.im_pos; positivity) (by positivity)).2
  have h := mul_le_mul_of_nonneg_left hQuad
    (show 0 ≤ z.im * (2 * (D : ℝ)) ^ 2 by positivity)
  simpa only [crossHeightConstant, mul_assoc, mul_left_comm, mul_comm] using h

end
end ManuscriptAudit.Paper8OddCrossPoincareHeight

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossPoincareHeight.scaledCross_translate_height_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
