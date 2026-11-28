import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8RectangleCurrentGreen
import PrimalitySheafVerification.ManuscriptAudit.Paper8CurvedGreenChart

/-! Green's formula with the actual variable lower limit in the physical half-plane coordinates. -/

namespace ManuscriptAudit.Paper8CurvedCurrentGreen

open Set MeasureTheory MaassLaplacian RectangularIntegral Paper8CurvedGreenChart
open scoped Interval

noncomputable section

def curl (J : ℂ → ℂ) (x y : ℝ) : ℂ :=
  Complex.I * fderiv ℝ J (complexPoint x y) 1 - fderiv ℝ J (complexPoint x y) Complex.I

theorem green_identity {a b Y : ℝ} (hab : a ≤ b) (J : ℂ → ℂ) (lower : ℝ → ℝ)
    (hLower : ∀ x ∈ Icc a b, DifferentiableAt ℝ lower x)
    (hJ : ∀ x ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ J (point lower Y x t))
    (hX : ContinuousOn (rateX J lower Y).uncurry (rectangle a b 0 1))
    (hT : ContinuousOn (rateT J lower Y).uncurry (rectangle a b 0 1)) :
    (∫ x in a..b, ∫ y in lower x..Y, curl J x y) =
      (∫ t in (0 : ℝ)..1, pullbackT J lower Y b t - pullbackT J lower Y a t) -
        (∫ x in a..b, pullbackX J lower Y x 1 - pullbackX J lower Y x 0) := by
  have hBox := Paper8RectangleCurrentGreen.green_identity hab (zero_le_one : (0 : ℝ) ≤ 1)
    (pullbackX J lower Y) (pullbackT J lower Y) (rateX J lower Y) (rateT J lower Y) hX hT
    (fun x hx t ht => pullbackT_hasDerivAt_x (hLower x hx) (hJ x hx t ht))
    (fun x hx t ht => pullbackX_hasDerivAt_t (hJ x hx t ht))
  change box a b 0 1 ((rateX J lower Y).uncurry - (rateT J lower Y).uncurry) = _ at hBox
  rw [box_columns hab (zero_le_one : (0 : ℝ) ≤ 1) (hX.sub hT)] at hBox
  rw [← hBox]
  apply intervalIntegral.integral_congr
  intro x _
  calc
    (∫ y in lower x..Y, curl J x y) =
        ((Y - lower x : ℝ) : ℂ) *
          (∫ t in (0 : ℝ)..1, curl J x ((Y - lower x) * t + lower x)) := by
      symm
      simpa only [Complex.real_smul, mul_zero, zero_add, mul_one, sub_add_cancel] using
        (intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
          (curl J x) (Y - lower x) (lower x))
    _ = ∫ t in (0 : ℝ)..1, rateX J lower Y x t - rateT J lower Y x t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      rw [rates_sub]
      have hHeight : height lower Y x t = (Y - lower x) * t + lower x := by
        unfold height
        ring
      rw [point, hHeight, curl]

end
end ManuscriptAudit.Paper8CurvedCurrentGreen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8CurvedCurrentGreen.green_identity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
