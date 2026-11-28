import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossLocalizedKernel

/-! Unfold the actual height-truncated incomplete cross Poincaré term row by row. -/

namespace ManuscriptAudit.Paper8OddCrossLocalizedRows

open Set Filter MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8OddCrossLocalizedKernel Paper8OddCrossPoincareUnfold
open Paper8OddCrossPoincareKernel Paper8OddCrossPoincareHeight Paper8OddCrossPoincareConvergence
open Paper8OddCrossPoincareTranslate Paper8OddCrossPoincareRowKernel Paper8OddCrossScaledRows
open Paper8OddCrossCuspNormalization Paper8OddCrossCuspPhase Paper8OddCrossCuspActualMultiplier
open Paper8OddCrossCuspCutoff
open scoped MatrixGroups

noncomputable section

theorem crossInvertedHeight_continuous {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Continuous (crossInvertedHeight y c) := by
  unfold crossInvertedHeight
  exact continuous_const.div (continuous_const.mul ((continuous_id.pow 2).add continuous_const))
    (fun _ => by positivity)

theorem crossRealKernel_two_eq (y c u : ℝ) :
    crossRealKernel 2 y c u =
      ((crossInvertedHeight y c u : ℝ) : ℂ) ^ (2 : ℕ) * crossRealKernel 0 y c u := by
  unfold crossRealKernel crossInvertedHeight
  simp only [Complex.cpow_two, Complex.cpow_zero, mul_one]
  ring

theorem norm_crossHeightCutoffKernel_le {q y c : ℝ} (hq : 0 < q) (u : ℝ) :
    ‖crossHeightCutoffKernel q y c u‖ ≤ (q ^ 2)⁻¹ * ‖crossRealKernel 2 y c u‖ := by
  by_cases h : q < crossInvertedHeight y c u
  · rw [crossHeightCutoffKernel, if_pos h, crossRealKernel_two_eq, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq.trans h), ← mul_assoc]
    have hOne : 1 ≤ (q ^ 2)⁻¹ * crossInvertedHeight y c u ^ 2 := by
      rw [mul_comm, ← div_eq_mul_inv, one_le_div (sq_pos_of_pos hq)]
      exact pow_le_pow_left₀ hq.le h.le 2
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hOne (norm_nonneg (crossRealKernel 0 y c u))
  · rw [crossHeightCutoffKernel, if_neg h, norm_zero]
    positivity

theorem crossHeightCutoffKernel_measurable (q : ℝ) {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Measurable (crossHeightCutoffKernel q y c) := by
  have hSet : MeasurableSet {u : ℝ | q < crossInvertedHeight y c u} :=
    (isOpen_lt continuous_const (crossInvertedHeight_continuous hy hc)).measurableSet
  exact (crossRealKernel_continuous 0 hy hc).measurable.piecewise hSet measurable_const

theorem crossHeightCutoffKernel_integrable {q y c : ℝ} (hq : 0 < q) (hy : 0 < y) (hc : 0 < c) :
    Integrable (crossHeightCutoffKernel q y c) := by
  have hInt := crossRealKernel_integrable 2 (by norm_num) hy hc
  exact (hInt.norm.const_mul ((q ^ 2)⁻¹)).mono'
    (crossHeightCutoffKernel_measurable q hy hc).aestronglyMeasurable
    (Eventually.of_forall (norm_crossHeightCutoffKernel_le hq))

def oddCrossHeightCutoffFourierTerm (q : ℝ) (z : ℍ) (i : CrossIndex) : ℂ :=
  if q < (scaledCrossMatrix i.2.1 • translatePoint i.2.2 z).im then oddCrossFourierTerm 0 z i else 0

theorem oddCrossFourierTerm_translated_kernel {D : ℕ} (A : CrossRow (D + 1)) (n : ℤ) (s : ℂ)
    (z : ℍ) :
    oddCrossFourierTerm s z ⟨D, A, n⟩ =
      crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1) *
      crossRealKernel s z.im (2 * ((D + 1 : ℕ) : ℝ)) ((n : ℝ) + z.re + crossRowShift A) := by
  rw [oddCrossFourierTerm_translate A n s z, oddCrossFourierTerm_row_kernel, translatePoint_re]
  have hIm : (translatePoint n z).im = z.im := by
    change ((translatePoint n z : ℍ) : ℂ).im = z.im
    rw [translatePoint_coe, Complex.add_im, Complex.intCast_im, zero_add] <;> rfl
  rw [hIm]

theorem oddCrossHeightCutoffFourierTerm_kernel {D : ℕ} (A : CrossRow (D + 1)) (n : ℤ) (q : ℝ)
    (z : ℍ) :
    oddCrossHeightCutoffFourierTerm q z ⟨D, A, n⟩ =
      crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1) *
      crossHeightCutoffKernel q z.im (2 * ((D + 1 : ℕ) : ℝ)) ((n : ℝ) + z.re + crossRowShift A) := by
  unfold oddCrossHeightCutoffFourierTerm
  dsimp only
  rw [scaledCross_translate_height (Nat.succ_pos D), oddCrossFourierTerm_translated_kernel,
    crossHeightCutoffKernel, crossInvertedHeight]
  split_ifs <;> simp

theorem norm_oddCrossHeightCutoffFourierTerm_le {q : ℝ} (hq : 0 < q) (z : ℍ) (i : CrossIndex) :
    ‖oddCrossHeightCutoffFourierTerm q z i‖ ≤ (q ^ 2)⁻¹ * ‖oddCrossFourierTerm 2 z i‖ := by
  rcases i with ⟨D, A, n⟩
  rw [oddCrossHeightCutoffFourierTerm_kernel, oddCrossFourierTerm_translated_kernel, norm_mul, norm_mul,
    mul_left_comm ((q ^ 2)⁻¹)]
  exact mul_le_mul_of_nonneg_left (norm_crossHeightCutoffKernel_le hq _) (norm_nonneg _)

theorem oddCrossHeightCutoffFourierTerm_measurable (q : ℝ) {y : ℝ} (hy : 0 < y) (i : CrossIndex) :
    Measurable (fun x : ℝ => oddCrossHeightCutoffFourierTerm q (pointAtHeight x hy) i) := by
  rcases i with ⟨D, A, n⟩
  have hEq (x : ℝ) :
      oddCrossHeightCutoffFourierTerm q (pointAtHeight x hy) ⟨D, A, n⟩ =
      crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1) *
      crossHeightCutoffKernel q y (2 * ((D + 1 : ℕ) : ℝ)) ((n : ℝ) + x + crossRowShift A) := by
    rw [oddCrossHeightCutoffFourierTerm_kernel, pointAtHeight_im, pointAtHeight_re]
  simp_rw [hEq]
  exact measurable_const.mul ((crossHeightCutoffKernel_measurable q hy (by positivity)).comp
    ((measurable_const.add measurable_id).add measurable_const))

theorem hasSum_oddCrossHeightCutoff_row_fourier {D : ℕ} (A : CrossRow (D + 1)) {q y : ℝ}
    (hq : 0 < q) (hy : 0 < y) :
    HasSum (fun n : ℤ => ∫ x in (0 : ℝ)..(1 : ℝ),
      oddCrossHeightCutoffFourierTerm q (pointAtHeight x hy) ⟨D, A, n⟩)
      (crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1) *
      ∫ u : ℝ, crossHeightCutoffKernel q y (2 * ((D + 1 : ℕ) : ℝ)) u) := by
  let K := crossHeightCutoffKernel q y (2 * ((D + 1 : ℕ) : ℝ))
  let b := crossRowShift A
  let a := crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1)
  have hInt : Integrable K := crossHeightCutoffKernel_integrable hq hy (by positivity)
  refine ((hInt.hasSum_intervalIntegral b).mul_left a).congr_fun (fun n => ?_)
  rw [← intervalIntegral.integral_const_mul]
  have hTr : (∫ x in (0 : ℝ)..(1 : ℝ), a * K (x + (b + (n : ℝ)))) =
      ∫ u in b + (n : ℝ)..b + (n : ℝ) + 1, a * K u := by
    simpa only [zero_add, add_comm (1 : ℝ)] using
      intervalIntegral.integral_comp_add_right (a := 0) (b := 1) (f := fun u => a * K u) (b + (n : ℝ))
  rw [← hTr]
  apply intervalIntegral.integral_congr
  intro x _
  rw [oddCrossHeightCutoffFourierTerm_kernel, pointAtHeight_re, pointAtHeight_im]
  change a * K ((n : ℝ) + x + b) = a * K (x + (b + (n : ℝ)))
  rw [show (n : ℝ) + x + b = x + (b + (n : ℝ)) by ring]

end
end ManuscriptAudit.Paper8OddCrossLocalizedRows

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossLocalizedRows.oddCrossHeightCutoffFourierTerm_kernel,
      ``ManuscriptAudit.Paper8OddCrossLocalizedRows.hasSum_oddCrossHeightCutoff_row_fourier] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
