import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassChartExtension
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassGraphNorm

/-! Bound the total Euclidean core derivative energy of the actual odd charts by their covariant graph norm. -/

namespace ManuscriptAudit.Paper8OddMaassCoreDerivativeBound

open MeasureTheory Set UpperHalfPlane MaassLaplacian
open Paper8OddMaassHilbertCore Paper8OddMaassEnergyCompletion Paper8OddMaassGraphNorm
open Paper8MaassCovariantGeometry Paper8MaassCovariantPullback
open Paper8OddCosetChartTransition Paper8OddCosetChartEnergy
open Paper8OddMaassHorizontalPoincare Paper8OddMaassLevelFourTail Paper8OddMaassCuspTailEstimate
open Paper8OddMaassChartExtension Paper8ModularCoreRectangle Paper8ModularCoreIntegral
open FiniteIndexWeightZeroCosets
open scoped ENNReal MatrixGroups

noncomputable section

private theorem derivative_norm_sq_sum_le_covariant (F : ℂ → ℂ) (z : ℍ) {B : ℝ}
    (hB : 0 < B) (hZ : B ≤ z.im) :
    ‖fderiv ℝ F (z : ℂ) 1‖ ^ 2 + ‖fderiv ℝ F (z : ℂ) Complex.I‖ ^ 2 ≤
      (3 / B ^ 2) * (maassCovariantEnergy F z + ‖F z‖ ^ 2) := by
  let R := maassCovariantEnergy F z + ‖F z‖ ^ 2
  have hR : 0 ≤ R := by unfold R maassCovariantEnergy; positivity
  have hC : ‖maassCovariantValue F z Complex.I‖ ^ 2 =
      z.im ^ 2 * ‖fderiv ℝ F (z : ℂ) Complex.I‖ ^ 2 := by
    unfold maassCovariantValue
    simp only [Complex.I_re, Complex.ofReal_zero, mul_zero, zero_mul, add_zero,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.im_pos, mul_pow]
  have hY : ‖fderiv ℝ F (z : ℂ) Complex.I‖ ^ 2 =
      ‖maassCovariantValue F z Complex.I‖ ^ 2 / z.im ^ 2 := by
    apply (eq_div_iff (sq_pos_of_pos z.im_pos).ne').2
    rw [hC, mul_comm]
  have hCR : ‖maassCovariantValue F z Complex.I‖ ^ 2 ≤ R := by
    unfold R maassCovariantEnergy
    nlinarith only [sq_nonneg ‖maassCovariantValue F z 1‖, sq_nonneg ‖F z‖]
  have hYle : ‖fderiv ℝ F (z : ℂ) Complex.I‖ ^ 2 ≤ (1 / z.im ^ 2) * R := by
    rw [hY, one_div, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hCR (inv_nonneg.mpr (sq_nonneg _))
  have hZsq := pow_le_pow_left₀ hB.le hZ 2
  have h₂ : 2 / z.im ^ 2 ≤ 2 / B ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hB) hZsq
  have h₁ : 1 / z.im ^ 2 ≤ 1 / B ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hB) hZsq
  calc
    _ ≤ (2 / z.im ^ 2) * R + (1 / z.im ^ 2) * R :=
      add_le_add (horizontal_derivative_norm_sq_le_covariant F z) hYle
    _ ≤ (2 / B ^ 2) * R + (1 / B ^ 2) * R :=
      add_le_add (mul_le_mul_of_nonneg_right h₂ hR) (mul_le_mul_of_nonneg_right h₁ hR)
    _ = _ := by ring

def extendedOddChartDerivativeSquare (f : OddSmoothCompactCore)
    (q : levelFourRightCoset) (p : ℝ × ℝ) : ℝ :=
  ‖extendedOddChartX f q p.1 p.2‖ ^ 2 + ‖extendedOddChartY f q p.1 p.2‖ ^ 2

theorem extendedOddChartDerivativeSquare_nonneg (f : OddSmoothCompactCore)
    (q : levelFourRightCoset) (p : ℝ × ℝ) : 0 ≤ extendedOddChartDerivativeSquare f q p := by
  unfold extendedOddChartDerivativeSquare
  positivity

theorem continuous_extendedOddChartDerivativeSquare (f : OddSmoothCompactCore) (q : levelFourRightCoset) :
    Continuous (extendedOddChartDerivativeSquare f q) :=
  ((continuous_extendedOddChartX f q).norm.pow 2).add ((continuous_extendedOddChartY f q).norm.pow 2)

theorem sum_coreChartDerivativeSquare_le (f : OddSmoothCompactCore) {p : ℝ × ℝ}
    (hp : coreMinimumHeight ≤ p.2) :
    letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
    (∑ q : levelFourRightCoset, extendedOddChartDerivativeSquare f q p) ≤
      (3 / coreMinimumHeight ^ 2) * oddCosetChartTotalEnergy f (coreCoordinatePoint p) := by
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  let z := coreCoordinatePoint p
  have hz : coreMinimumHeight ≤ z.im := by
    change coreMinimumHeight ≤ (complexPoint p.1 (max p.2 coreMinimumHeight)).im
    rw [complexPoint_im, max_eq_left hp]
    exact hp
  dsimp only
  calc
    _ ≤ ∑ q : levelFourRightCoset, (3 / coreMinimumHeight ^ 2) *
      (maassCovariantEnergy (oddCosetPullback f q) z + ‖oddCosetPullback f q z‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro q _
        unfold extendedOddChartDerivativeSquare
        rw [extendedOddChartX_eq_on_core f q hp, extendedOddChartY_eq_on_core f q hp]
        exact derivative_norm_sq_sum_le_covariant (oddCosetPullback f q) z coreMinimumHeight_pos hz
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [oddCosetChartTotalEnergy, oddCosetChartEnergyAt, oddCosetChartMassAt,
        oddCosetPullback_coe, z]

theorem sum_lintegral_coreChartDerivativeSquare_le (f : OddSmoothCompactCore) (T : ℝ) :
    letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
    (∑ q : levelFourRightCoset, ∫⁻ p in euclideanCoreRectangle T,
      ENNReal.ofReal (extendedOddChartDerivativeSquare f q p)) ≤
      ENNReal.ofReal (3 / coreMinimumHeight ^ 2) * ENNReal.ofReal (T ^ 2) * 2 *
        (Fintype.card levelFourRightCoset : ℝ≥0∞) * ENNReal.ofReal (‖oddCoreEnergyGraph f‖ ^ 2) := by
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  let E (z : ℍ) := ENNReal.ofReal (oddCosetChartTotalEnergy f z)
  let C := ENNReal.ofReal (3 / coreMinimumHeight ^ 2)
  let R := euclideanCoreRectangle T
  have hE : Measurable E := ENNReal.measurable_ofReal.comp (continuous_oddCosetChartTotalEnergy f).measurable
  have hInv (g : SL(2, ℤ)) (z : ℍ) : E (g • z) = E z := by
    unfold E
    rw [oddCosetChartTotalEnergy_invariant]
  have hR : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hD (q : levelFourRightCoset) : Measurable (fun p => ENNReal.ofReal (extendedOddChartDerivativeSquare f q p)) :=
    ENNReal.measurable_ofReal.comp (continuous_extendedOddChartDerivativeSquare f q).measurable
  dsimp only
  calc
    _ = ∫⁻ p in R, ENNReal.ofReal (∑ q : levelFourRightCoset, extendedOddChartDerivativeSquare f q p) := by
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => extendedOddChartDerivativeSquare_nonneg f q _)]
      exact (lintegral_finsetSum _ (fun q _ => hD q)).symm
    _ ≤ ∫⁻ p in R, C * E (coreCoordinatePoint p) := by
      apply setLIntegral_mono' hR
      intro p hp
      have h := ENNReal.ofReal_le_ofReal (sum_coreChartDerivativeSquare_le f hp.2.1)
      simpa only [C, E, ENNReal.ofReal_mul (div_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg _))] using h
    _ = C * ∫⁻ p in R, E (coreCoordinatePoint p) :=
      lintegral_const_mul _ (hE.comp continuous_coreCoordinatePoint.measurable)
    _ ≤ C * (ENNReal.ofReal (T ^ 2) * ∫⁻ z in modularCoreRectangle T, E z) :=
      mul_le_mul_left' (lintegral_euclideanCore_le_hyperbolic hE T) _
    _ ≤ C * (ENNReal.ofReal (T ^ 2) * (2 * ∫⁻ z in ModularGroup.fd, E z)) :=
      mul_le_mul_left' (mul_le_mul_left' (lintegral_modularCoreRectangle_le_two hInv T) _) _
    _ ≤ _ := by
      simp only [C, mul_assoc]
      apply mul_le_mul_left'
      apply mul_le_mul_left'
      apply mul_le_mul_left'
      rw [← oddCoreGraphDensity_lintegral_eq_graphNorm]
      exact lintegral_oddChartEnergy_le_levelFour f

end
end ManuscriptAudit.Paper8OddMaassCoreDerivativeBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassCoreDerivativeBound.sum_lintegral_coreChartDerivativeSquare_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
