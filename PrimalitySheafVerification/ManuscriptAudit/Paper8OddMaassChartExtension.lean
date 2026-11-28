import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassHorizontalPoincare
import PrimalitySheafVerification.ManuscriptAudit.Paper8ModularCoreIntegral

/-! A globally differentiable extension of the actual cusp charts on the bounded core rectangle. -/

namespace ManuscriptAudit.Paper8OddMaassChartExtension

open Filter Set UpperHalfPlane MaassLaplacian
open Paper8ModularCoreRectangle Paper8ModularCoreIntegral
open Paper8OddMaassHorizontalPoincare Paper8OddMaassHilbertCore
open Paper8OddCosetChartTransition Paper8OddCosetChartEnergy Paper8OddCosetChartDifferential
open scoped Topology

noncomputable section

private def chartCutoff (y : ℝ) : ℝ :=
  Real.smoothTransition ((y - coreMinimumHeight / 2) / (coreMinimumHeight / 4))

private theorem chartCutoff_contDiff : ContDiff ℝ 1 chartCutoff := by
  unfold chartCutoff
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

private theorem chartCutoff_eq_zero {y : ℝ} (h : y ≤ coreMinimumHeight / 2) : chartCutoff y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by linarith [coreMinimumHeight_pos])

private theorem chartCutoff_eq_one {y : ℝ} (h : 3 * coreMinimumHeight / 4 ≤ y) :
    chartCutoff y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (by linarith [coreMinimumHeight_pos])).mpr (by linarith)

private theorem chartCutoff_deriv_eq_zero_low {y : ℝ} (h : y < coreMinimumHeight / 2) :
    deriv chartCutoff y = 0 := by
  have hEq : chartCutoff =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds h] with t ht
    exact chartCutoff_eq_zero ht.le
  rw [hEq.deriv_eq, deriv_const]

private theorem chartCutoff_deriv_eq_zero_high {y : ℝ} (h : 3 * coreMinimumHeight / 4 < y) :
    deriv chartCutoff y = 0 := by
  have hEq : chartCutoff =ᶠ[𝓝 y] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds h] with t ht
    exact chartCutoff_eq_one ht.le
  rw [hEq.deriv_eq, deriv_const]

private def clampHeight : ℝ := coreMinimumHeight / 8

private theorem clampHeight_pos : 0 < clampHeight := by
  unfold clampHeight
  linarith [coreMinimumHeight_pos]

private def extensionPoint (x y : ℝ) : ℍ :=
  horizontalUpperPoint x (clampHeight_pos.trans_le (le_max_right y clampHeight))

private theorem continuous_extensionPoint : Continuous (fun p : ℝ × ℝ => extensionPoint p.1 p.2) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun p : ℝ × ℝ => complexPoint p.1 (max p.2 clampHeight))
  unfold complexPoint
  fun_prop

def extendedOddChart (f : OddSmoothCompactCore) (q : levelFourRightCoset) (x y : ℝ) : ℂ :=
  (chartCutoff y : ℂ) * oddCosetPullback f q (extensionPoint x y)

def extendedOddChartX (f : OddSmoothCompactCore) (q : levelFourRightCoset) (x y : ℝ) : ℂ :=
  (chartCutoff y : ℂ) * fderiv ℝ (oddCosetPullback f q) (extensionPoint x y : ℂ) 1

def extendedOddChartY (f : OddSmoothCompactCore) (q : levelFourRightCoset) (x y : ℝ) : ℂ :=
  (deriv chartCutoff y : ℂ) * oddCosetPullback f q (extensionPoint x y) +
    (chartCutoff y : ℂ) * fderiv ℝ (oddCosetPullback f q) (extensionPoint x y : ℂ) Complex.I

theorem continuous_extendedOddChart (f : OddSmoothCompactCore) (q : levelFourRightCoset) :
    Continuous (fun p : ℝ × ℝ => extendedOddChart f q p.1 p.2) := by
  unfold extendedOddChart
  exact (Complex.continuous_ofReal.comp (chartCutoff_contDiff.continuous.comp continuous_snd)).mul
    ((oddCosetPullback_continuous f q).comp continuous_extensionPoint)

theorem continuous_extendedOddChartX (f : OddSmoothCompactCore) (q : levelFourRightCoset) :
    Continuous (fun p : ℝ × ℝ => extendedOddChartX f q p.1 p.2) := by
  unfold extendedOddChartX
  exact (Complex.continuous_ofReal.comp (chartCutoff_contDiff.continuous.comp continuous_snd)).mul
    ((oddCosetPullback_directional_continuous f q 1).comp continuous_extensionPoint)

theorem continuous_extendedOddChartY (f : OddSmoothCompactCore) (q : levelFourRightCoset) :
    Continuous (fun p : ℝ × ℝ => extendedOddChartY f q p.1 p.2) := by
  unfold extendedOddChartY
  exact ((Complex.continuous_ofReal.comp (chartCutoff_contDiff.continuous_deriv_one.comp continuous_snd)).mul
      ((oddCosetPullback_continuous f q).comp continuous_extensionPoint)).add
    ((Complex.continuous_ofReal.comp (chartCutoff_contDiff.continuous.comp continuous_snd)).mul
      ((oddCosetPullback_directional_continuous f q Complex.I).comp continuous_extensionPoint))

theorem extendedOddChart_hasDerivAt_x (f : OddSmoothCompactCore) (q : levelFourRightCoset) (x y : ℝ) :
    HasDerivAt (fun t => extendedOddChart f q t y) (extendedOddChartX f q x y) x := by
  exact (oddCosetPullback_hasDerivAt f q x (clampHeight_pos.trans_le (le_max_right y clampHeight))).const_mul _

theorem extendedOddChart_hasDerivAt_y (f : OddSmoothCompactCore) (q : levelFourRightCoset) (x y : ℝ) :
    HasDerivAt (fun t => extendedOddChart f q x t) (extendedOddChartY f q x y) y := by
  by_cases h : clampHeight < y
  · have hy : 0 < y := clampHeight_pos.trans h
    let z := horizontalUpperPoint x hy
    have hPoint : extensionPoint x y = z := by
      apply UpperHalfPlane.ext
      change complexPoint x (max y clampHeight) = complexPoint x y
      rw [max_eq_left h.le]
    have hA : HasDerivAt (fun t => complexPoint x t) Complex.I y := by
      simpa only [id_eq, mul_one] using vertical_derivative (hasDerivAt_id (complexPoint x y))
    have hB : HasDerivAt (fun t => oddCosetPullback f q (complexPoint x t))
        (fderiv ℝ (oddCosetPullback f q) (z : ℂ) Complex.I) y :=
      (oddCosetPullback_differentiableAt f q z).hasFDerivAt.comp_hasDerivAt y hA
    have hC : HasDerivAt chartCutoff (deriv chartCutoff y) y :=
      (chartCutoff_contDiff.differentiable (by norm_num) y).hasDerivAt
    have hLoc :
        (fun t => extendedOddChart f q x t) =ᶠ[𝓝 y]
          (fun t => (chartCutoff t : ℂ) * oddCosetPullback f q (complexPoint x t)) := by
      filter_upwards [Ioi_mem_nhds h] with t ht
      unfold extendedOddChart
      change (chartCutoff t : ℂ) * oddCosetPullback f q (complexPoint x (max t clampHeight)) = _
      rw [max_eq_left ht.le]
    have hProduct := (hC.ofReal_comp.mul hB).congr_of_eventuallyEq hLoc
    simpa only [extendedOddChartY, hPoint] using hProduct
  · have hLow : y < coreMinimumHeight / 2 := by
      have hY : y ≤ clampHeight := not_lt.mp h
      unfold clampHeight at hY
      linarith [coreMinimumHeight_pos]
    have hV : extendedOddChartY f q x y = 0 := by
      unfold extendedOddChartY
      simp only [chartCutoff_eq_zero hLow.le, chartCutoff_deriv_eq_zero_low hLow,
        Complex.ofReal_zero, zero_mul, add_zero]
    have hLoc : (fun t => extendedOddChart f q x t) =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) := by
      filter_upwards [Iio_mem_nhds hLow] with t ht
      unfold extendedOddChart
      simp only [chartCutoff_eq_zero ht.le, Complex.ofReal_zero, zero_mul]
    rw [hV]
    exact (hasDerivAt_const y (0 : ℂ)).congr_of_eventuallyEq hLoc

private theorem extensionPoint_eq_coreCoordinatePoint {p : ℝ × ℝ} (hp : coreMinimumHeight ≤ p.2) :
    extensionPoint p.1 p.2 = coreCoordinatePoint p := by
  have hSmall : clampHeight ≤ p.2 := by
    unfold clampHeight
    linarith [coreMinimumHeight_pos]
  apply UpperHalfPlane.ext
  change complexPoint p.1 (max p.2 clampHeight) = complexPoint p.1 (max p.2 coreMinimumHeight)
  rw [max_eq_left hSmall, max_eq_left hp]

theorem extendedOddChart_eq_on_core (f : OddSmoothCompactCore) (q : levelFourRightCoset)
    {p : ℝ × ℝ} (hp : coreMinimumHeight ≤ p.2) :
    extendedOddChart f q p.1 p.2 = oddCosetPullback f q (coreCoordinatePoint p) := by
  have hOne : 3 * coreMinimumHeight / 4 ≤ p.2 := by linarith [coreMinimumHeight_pos]
  simp only [extendedOddChart, chartCutoff_eq_one hOne, Complex.ofReal_one, one_mul,
    extensionPoint_eq_coreCoordinatePoint hp]

theorem extendedOddChartX_eq_on_core (f : OddSmoothCompactCore) (q : levelFourRightCoset)
    {p : ℝ × ℝ} (hp : coreMinimumHeight ≤ p.2) :
    extendedOddChartX f q p.1 p.2 = fderiv ℝ (oddCosetPullback f q) (coreCoordinatePoint p : ℂ) 1 := by
  have hOne : 3 * coreMinimumHeight / 4 ≤ p.2 := by linarith [coreMinimumHeight_pos]
  simp only [extendedOddChartX, chartCutoff_eq_one hOne, Complex.ofReal_one, one_mul,
    extensionPoint_eq_coreCoordinatePoint hp]

theorem extendedOddChartY_eq_on_core (f : OddSmoothCompactCore) (q : levelFourRightCoset)
    {p : ℝ × ℝ} (hp : coreMinimumHeight ≤ p.2) :
    extendedOddChartY f q p.1 p.2 = fderiv ℝ (oddCosetPullback f q) (coreCoordinatePoint p : ℂ) Complex.I := by
  have hOne : 3 * coreMinimumHeight / 4 < p.2 := by linarith [coreMinimumHeight_pos]
  simp only [extendedOddChartY, chartCutoff_eq_one hOne.le, chartCutoff_deriv_eq_zero_high hOne,
    Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, zero_add,
    extensionPoint_eq_coreCoordinatePoint hp]

end
end ManuscriptAudit.Paper8OddMaassChartExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddMaassChartExtension.extendedOddChart_hasDerivAt_x,
      ``ManuscriptAudit.Paper8OddMaassChartExtension.extendedOddChart_hasDerivAt_y,
      ``ManuscriptAudit.Paper8OddMaassChartExtension.extendedOddChartY_eq_on_core] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
