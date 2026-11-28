import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8CurvedCurrentGreen
import PrimalitySheafVerification.ManuscriptAudit.Paper8StandardDomainSidePairing

/-! Stokes on the actual standard modular domain with its paired sides and horizontal cutoff. -/

namespace ManuscriptAudit.Paper8StandardDomainCurrentGreen

open Set MeasureTheory UpperHalfPlane ModularForm MaassLaplacian RectangularIntegral
open Paper8CurvedGreenChart Paper8CurvedCurrentGreen Paper8StandardDomainSidePairing
open scoped MatrixGroups ModularForm Interval

noncomputable section

def asComplexCurrent (f : ℍ → ℂ) (w : ℂ) : ℂ := f (ofComplex w)

private theorem left_to_right (y : ℝ) (hy : 0 < y) :
    ModularGroup.T • ofComplex (complexPoint (-(1 / 2)) y) =
      ofComplex (complexPoint (1 / 2) y) := by
  have hl : 0 < (complexPoint (-(1 / 2)) y).im := by rw [complexPoint_im]; exact hy
  have hr : 0 < (complexPoint (1 / 2) y).im := by rw [complexPoint_im]; exact hy
  rw [ofComplex_apply_of_im_pos hl, ofComplex_apply_of_im_pos hr]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_T_smul]
  unfold complexPoint
  push_cast
  ring

theorem integral_curl_zero (f : ℍ → ℂ) {Y : ℝ} (hY : 1 ≤ Y)
    (hT : f ∣[(2 : ℤ)] ModularGroup.T = f) (hS : f ∣[(2 : ℤ)] ModularGroup.S = f)
    (hTop : ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), f (ofComplex (complexPoint x Y)) = 0)
    (hJ : ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (asComplexCurrent f) (point arcHeight Y x t))
    (hX : ContinuousOn (rateX (asComplexCurrent f) arcHeight Y).uncurry
      (rectangle (-(1 / 2)) (1 / 2) 0 1))
    (hRateT : ContinuousOn (rateT (asComplexCurrent f) arcHeight Y).uncurry
      (rectangle (-(1 / 2)) (1 / 2) 0 1)) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), ∫ y in arcHeight x..Y, curl (asComplexCurrent f) x y) = 0 := by
  have hab : (-(1 / 2) : ℝ) ≤ 1 / 2 := by norm_num
  have hLow : arcHeight (-(1 / 2)) = arcHeight (1 / 2) := arcHeight_neg _
  have hLeftRight : (∫ t in (0 : ℝ)..1,
      pullbackT (asComplexCurrent f) arcHeight Y (1 / 2) t -
        pullbackT (asComplexCurrent f) arcHeight Y (-(1 / 2)) t) = 0 := by
    calc
      _ = ∫ _ in (0 : ℝ)..1, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at ht
        let y := height arcHeight Y (1 / 2) t
        have hyPos : 0 < y := by
          have hArc : 0 < arcHeight (1 / 2) := arcHeight_pos (by norm_num)
          have hArc1 : arcHeight (1 / 2) ≤ 1 := by unfold arcHeight; exact Real.sqrt_le_one.2 (by norm_num)
          exact add_pos_of_pos_of_nonneg hArc (mul_nonneg ht.1 (sub_nonneg.mpr (hArc1.trans hY)))
        have hHeight : height arcHeight Y (-(1 / 2)) t = y := by
          unfold height y
          rw [hLow]
        have hPair := left_to_right y hyPos
        simp only [pullbackT, point, asComplexCurrent, hLow, hHeight]
        change Complex.I * ((Y - arcHeight (1 / 2) : ℝ) : ℂ) *
            f (ofComplex (complexPoint (1 / 2) y)) -
          Complex.I * ((Y - arcHeight (1 / 2) : ℝ) : ℂ) *
            f (ofComplex (complexPoint (-(1 / 2)) y)) = 0
        rw [← hPair, weightTwo_T_invariant hT, sub_self]
      _ = _ := intervalIntegral.integral_zero
  have hTopBottom : (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ),
      pullbackX (asComplexCurrent f) arcHeight Y x 1 -
        pullbackX (asComplexCurrent f) arcHeight Y x 0) = 0 := by
    calc
      _ = ∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), -arcCurrent f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        have hA : |x| ≤ 1 / 2 := abs_le.mpr hx
        have hHeight : height arcHeight Y x 1 = Y := by unfold height; ring
        have hP : pullbackX (asComplexCurrent f) arcHeight Y x 1 = 0 := by
          simp [pullbackX, point, hHeight, asComplexCurrent, hTop x hx]
        have hQ : pullbackX (asComplexCurrent f) arcHeight Y x 0 = arcCurrent f x := by
          simp [pullbackX, point, height, slope, asComplexCurrent, arcCurrent, arcPoint,
            arcTangent_eq_derivative hA]
        rw [hP, hQ, zero_sub]
      _ = -(∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), arcCurrent f x) := intervalIntegral.integral_neg
      _ = _ := by rw [arcCurrent_integral_zero hS, neg_zero]
  have h := Paper8CurvedCurrentGreen.green_identity (Y := Y) hab (asComplexCurrent f) arcHeight
    (fun x hx => (arcHeight_hasDerivAt (abs_le.mpr hx)).differentiableAt) hJ hX hRateT
  rw [hLeftRight, hTopBottom, sub_zero] at h
  exact h

end
end ManuscriptAudit.Paper8StandardDomainCurrentGreen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8StandardDomainCurrentGreen.integral_curl_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
