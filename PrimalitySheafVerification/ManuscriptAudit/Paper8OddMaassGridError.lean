import Lean.Util.CollectAxioms
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassGridCells

/-! Sum the actual phase-corrected grid errors on the level-four cells. -/

namespace ManuscriptAudit.Paper8OddMaassGridError

open MeasureTheory Set
open Paper8OddMaassHilbertCore Paper8OddMaassEnergyCompletion Paper8OddMaassChartExtension
open Paper8OddCosetChartTransition Paper8ModularCoreRectangle Paper8ModularCoreIntegral
open Paper8RectangularGridApproximation Paper8RectangularIntegralMeasure
open Paper8OddMaassCoreDerivativeBound Paper8OddMaassGridCells Paper8RectangularCellApproximation
open FiniteIndexWeightZeroCosets
open scoped ENNReal

noncomputable section

private theorem gridCellError_nonneg (f : ℝ → ℝ → ℂ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    0 ≤ gridCellError f a b c d := by
  apply intervalIntegral.integral_nonneg hcd
  intro y _
  exact intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)

private theorem rectangleIntegral_add {f g : ℝ → ℝ → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    rectangleIntegral (fun x y => f x y + g x y) a b c d =
      rectangleIntegral f a b c d + rectangleIntegral g a b c d := by
  rw [rectangleIntegral_eq_setIntegral (hf.add hg) hab hcd, rectangleIntegral_eq_setIntegral hf hab hcd,
    rectangleIntegral_eq_setIntegral hg hab hcd]
  exact integral_add (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))

def oddGridCoefficient {n m : ℕ} (X Y : ℕ → ℝ) (f : OddSmoothCompactCore) (i : OddGridTile n m) : ℂ :=
  rectangularCellMean (extendedOddChart f i.1) (X i.2.1) (X (i.2.1.val + 1))
    (Y i.2.2) (Y (i.2.2.val + 1))

private theorem sum_real_gridCellError_cast {f : ℝ → ℝ → ℂ} {X Y : ℕ → ℝ}
    (hX : Monotone X) (hY : Monotone Y) (n m : ℕ) :
    (∑ i : Fin n, ∑ j : Fin m, ENNReal.ofReal (gridCellError f (X i) (X (i.val + 1)) (Y j) (Y (j.val + 1)))) =
      ENNReal.ofReal (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range n, gridCellError f (X i) (X (i + 1)) (Y j) (Y (j + 1))) := by
  rw [Finset.sum_comm]
  simp_rw [Fin.sum_univ_eq_sum_range]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => gridCellError_nonneg f
      (hX (Nat.le_succ i)) (hY (Nat.le_succ j)))]
  · intro j _
    exact Finset.sum_nonneg fun i _ => gridCellError_nonneg f
      (hX (Nat.le_succ i)) (hY (Nat.le_succ j))

theorem sum_oddGridCell_lintegral_error_le (f : OddSmoothCompactCore) {n m : ℕ}
    {T δ : ℝ} (X Y : ℕ → ℝ) (hX : StrictMono X) (hY : StrictMono Y)
    (hX₀ : X 0 = -(1 / 2)) (hXn : X n = 1 / 2)
    (hY₀ : Y 0 = coreMinimumHeight) (hYm : Y m = T)
    (hXδ : ∀ i < n, X (i + 1) - X i ≤ δ) (hYδ : ∀ j < m, Y (j + 1) - Y j ≤ δ) :
    letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
    (∑ i : OddGridTile n m, ∫⁻ z in oddGridCell X Y i,
          ENNReal.ofReal (‖(f : ℂ → ℂ) z - oddGridCoefficient X Y f i * oddGridPhase i z‖ ^ 2)) ≤
      ENNReal.ofReal ((coreMinimumHeight ^ 2)⁻¹) * ENNReal.ofReal (2 * δ ^ 2) *
        (ENNReal.ofReal (3 / coreMinimumHeight ^ 2) * ENNReal.ofReal (T ^ 2) * 2 *
          (Fintype.card levelFourRightCoset : ℝ≥0∞)) * ENNReal.ofReal (‖oddCoreEnergyGraph f‖ ^ 2) := by
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  let C := ENNReal.ofReal ((coreMinimumHeight ^ 2)⁻¹)
  let D := ENNReal.ofReal (2 * δ ^ 2)
  let η (i : OddGridTile n m) := ENNReal.ofReal (gridCellError (extendedOddChart f i.1)
    (X i.2.1) (X (i.2.1.val + 1)) (Y i.2.2) (Y (i.2.2.val + 1)))
  have hx : -(1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hy : coreMinimumHeight ≤ T := by simpa only [hY₀, hYm] using hY.monotone (Nat.zero_le m)
  have hQ (q : levelFourRightCoset) :
      (∑ i : Fin n, ∑ j : Fin m, η (q, i, j)) ≤
        D * ∫⁻ p in euclideanCoreRectangle T, ENNReal.ofReal (extendedOddChartDerivativeSquare f q p) := by
    let P := extendedOddChartX f q
    let Q := extendedOddChartY f q
    have hP := (continuous_extendedOddChartX f q).norm.pow 2
    have hQ := (continuous_extendedOddChartY f q).norm.pow 2
    have hGrid := sum_grid_cell_mean_error_le (continuous_extendedOddChart f q)
      (continuous_extendedOddChartX f q) (continuous_extendedOddChartY f q)
      (extendedOddChart_hasDerivAt_x f q) (extendedOddChart_hasDerivAt_y f q) hX hY n m hXδ hYδ
    rw [hX₀, hXn, hY₀, hYm] at hGrid
    change (∑ i : Fin n, ∑ j : Fin m, ENNReal.ofReal (gridCellError (extendedOddChart f q)
      (X i) (X (i.val + 1)) (Y j) (Y (j.val + 1)))) ≤ _
    rw [sum_real_gridCellError_cast hX.monotone hY.monotone n m]
    have hRI := ofReal_rectangleIntegral_eq_lintegral (hP.add hQ)
      (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) hx hy
    change ENNReal.ofReal (rectangleIntegral (fun x y => ‖P x y‖ ^ 2 + ‖Q x y‖ ^ 2)
      (-(1 / 2)) (1 / 2) coreMinimumHeight T) =
        ∫⁻ p in euclideanCoreRectangle T, ENNReal.ofReal (extendedOddChartDerivativeSquare f q p) at hRI
    rw [← hRI, ← ENNReal.ofReal_mul (show 0 ≤ 2 * δ ^ 2 by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [rectangleIntegral_add hP hQ hx hy, mul_add]
    exact hGrid
  dsimp only
  calc
    _ ≤ ∑ i : OddGridTile n m, C * η i := by
      apply Finset.sum_le_sum
      intro i _
      exact oddGridCell_lintegral_error_le X Y hX.monotone hY.monotone hY₀.ge f i
    _ = C * ∑ q : levelFourRightCoset, ∑ i : Fin n, ∑ j : Fin m, η (q, i, j) := by
      rw [← Finset.mul_sum]
      simp only [Fintype.sum_prod_type]
    _ ≤ C * (D * ∑ q : levelFourRightCoset, ∫⁻ p in euclideanCoreRectangle T,
        ENNReal.ofReal (extendedOddChartDerivativeSquare f q p)) := by
      apply mul_le_mul_left'
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun q _ => hQ q)
    _ ≤ _ := by
      simp only [C, D, mul_assoc]
      apply mul_le_mul_left'
      apply mul_le_mul_left'
      simpa only [mul_assoc] using sum_lintegral_coreChartDerivativeSquare_le f T

end
end ManuscriptAudit.Paper8OddMaassGridError

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassGridError.sum_oddGridCell_lintegral_error_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
