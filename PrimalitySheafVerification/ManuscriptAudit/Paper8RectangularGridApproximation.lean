import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8RectangularCellApproximation

/-! Sum the rectangular cell-mean errors over a finite grid with a uniform mesh bound. -/

namespace ManuscriptAudit.Paper8RectangularGridApproximation

open MeasureTheory Set
open Paper8RectangularCellApproximation Paper8ParametricCellMean

noncomputable section

def rectangleIntegral (f : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ y in c..d, ∫ x in a..b, f x y

theorem sum_grid_rectangleIntegral {f : ℝ → ℝ → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    {X Y : ℕ → ℝ} (hX : Monotone X) (n m : ℕ) :
    (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n,
      rectangleIntegral f (X i) (X (i + 1)) (Y j) (Y (j + 1))) =
      rectangleIntegral f (X 0) (X n) (Y 0) (Y m) := by
  let F (i : ℕ) (y : ℝ) := ∫ x in X i..X (i + 1), f x y
  have hF (i : ℕ) : Continuous (F i) := continuous_intervalIntegral_param hf (hX (Nat.le_succ i))
  have hW : Continuous (fun y => ∫ x in X 0..X n, f x y) :=
    continuous_intervalIntegral_param hf (hX (Nat.zero_le n))
  have hSlice (y : ℝ) : (∑ i ∈ Finset.range n, F i y) = ∫ x in X 0..X n, f x y :=
    intervalIntegral.sum_integral_adjacent_intervals fun i _ =>
      (hf.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have hRow (j : ℕ) :
      (∑ i ∈ Finset.range n, rectangleIntegral f (X i) (X (i + 1)) (Y j) (Y (j + 1))) =
        rectangleIntegral f (X 0) (X n) (Y j) (Y (j + 1)) := by
    change (∑ i ∈ Finset.range n, ∫ y in Y j..Y (j + 1), F i y) = _
    rw [← intervalIntegral.integral_finsetSum (fun i _ => (hF i).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro y _
    exact hSlice y
  simp_rw [hRow, rectangleIntegral]
  exact intervalIntegral.sum_integral_adjacent_intervals (fun j _ => hW.intervalIntegrable _ _)

def gridCellError (f : ℝ → ℝ → ℂ) (a b c d : ℝ) : ℝ :=
  rectangleIntegral (fun x y => ‖f x y - rectangularCellMean f a b c d‖ ^ 2) a b c d

theorem sum_grid_cell_mean_error_le {f Dₓ Dᵧ : ℝ → ℝ → ℂ}
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hDcₓ : Continuous (fun p : ℝ × ℝ => Dₓ p.1 p.2))
    (hDcᵧ : Continuous (fun p : ℝ × ℝ => Dᵧ p.1 p.2))
    (hDₓ : ∀ x y, HasDerivAt (fun t => f t y) (Dₓ x y) x)
    (hDᵧ : ∀ x y, HasDerivAt (fun t => f x t) (Dᵧ x y) y)
    {X Y : ℕ → ℝ} (hX : StrictMono X) (hY : StrictMono Y) (n m : ℕ) {δ : ℝ}
    (hXδ : ∀ i < n, X (i + 1) - X i ≤ δ) (hYδ : ∀ j < m, Y (j + 1) - Y j ≤ δ) :
    (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n,
      gridCellError f (X i) (X (i + 1)) (Y j) (Y (j + 1))) ≤
      (2 * δ ^ 2) * rectangleIntegral (fun x y => ‖Dₓ x y‖ ^ 2) (X 0) (X n) (Y 0) (Y m) +
      (2 * δ ^ 2) * rectangleIntegral (fun x y => ‖Dᵧ x y‖ ^ 2) (X 0) (X n) (Y 0) (Y m) := by
  let P (i j : ℕ) :=
    rectangleIntegral (fun x y => ‖Dₓ x y‖ ^ 2) (X i) (X (i + 1)) (Y j) (Y (j + 1))
  let Q (i j : ℕ) :=
    rectangleIntegral (fun x y => ‖Dᵧ x y‖ ^ 2) (X i) (X (i + 1)) (Y j) (Y (j + 1))
  have hP (i j : ℕ) : 0 ≤ P i j := by
    apply intervalIntegral.integral_nonneg (hY.monotone (Nat.le_succ j))
    intro y _
    exact intervalIntegral.integral_nonneg (hX.monotone (Nat.le_succ i)) (fun x _ => sq_nonneg _)
  have hQ (i j : ℕ) : 0 ≤ Q i j := by
    apply intervalIntegral.integral_nonneg (hY.monotone (Nat.le_succ j))
    intro y _
    exact intervalIntegral.integral_nonneg (hX.monotone (Nat.le_succ i)) (fun x _ => sq_nonneg _)
  have hCell (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < m) :
      gridCellError f (X i) (X (i + 1)) (Y j) (Y (j + 1)) ≤
        (2 * δ ^ 2) * P i j + (2 * δ ^ 2) * Q i j := by
    have hx : X i < X (i + 1) := hX (Nat.lt_succ_self i)
    have hy : Y j < Y (j + 1) := hY (Nat.lt_succ_self j)
    have hxδ := pow_le_pow_left₀ (sub_nonneg.mpr hx.le) (hXδ i hi) 2
    have hyδ := pow_le_pow_left₀ (sub_nonneg.mpr hy.le) (hYδ j hj) 2
    exact (rectangular_cell_mean_l2_error_le hf hDcₓ hDcᵧ hDₓ hDᵧ hx hy).trans
      (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxδ (by norm_num)) (hP i j))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyδ (by norm_num)) (hQ i j)))
  calc
    _ ≤ ∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n, (2 * δ ^ 2) * P i j + (2 * δ ^ 2) * Q i j := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact hCell i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, P, Q]
      rw [sum_grid_rectangleIntegral (hDcₓ.norm.pow 2) hX.monotone,
        sum_grid_rectangleIntegral (hDcᵧ.norm.pow 2) hX.monotone]

end
end ManuscriptAudit.Paper8RectangularGridApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8RectangularGridApproximation.sum_grid_cell_mean_error_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
