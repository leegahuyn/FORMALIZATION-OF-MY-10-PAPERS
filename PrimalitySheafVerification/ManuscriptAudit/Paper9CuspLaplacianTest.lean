import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import PrimalitySheafVerification.ManuscriptAudit.HyperbolicCuspGaugeTest
import PrimalitySheafVerification.ManuscriptAudit.Paper9PrintedLaplacianSign

/-! A compactly supported width-two cusp test has negative energy for the printed -Δ. -/

namespace ManuscriptAudit.Paper9CuspLaplacianTest

open MeasureTheory Set MaassLaplacian HyperbolicCuspGaugeTest
open Paper9PrintedLaplacianSign
open scoped UpperHalfPlane ContDiff

noncomputable section

def testCoordinates (_ y : ℝ) : ℂ := (cuspBump y : ℂ)

private theorem differentiable_bump : Differentiable ℝ cuspBump :=
  (contDiff_infty.mp cuspBump_smooth 1).differentiable (by decide)

private theorem contDiff_deriv : ContDiff ℝ 1 (deriv cuspBump) :=
  (contDiff_infty.mp cuspBump_smooth 2).deriv (by decide)

private theorem differentiable_deriv : Differentiable ℝ (deriv cuspBump) :=
  contDiff_deriv.differentiable (by decide)

@[simp] theorem test_partialX (x y : ℝ) : partialX testCoordinates x y = 0 := by
  simp [partialX, testCoordinates]

@[simp] theorem test_partialY (x y : ℝ) :
    partialY testCoordinates x y = (deriv cuspBump y : ℂ) :=
  ((differentiable_bump y).hasDerivAt.ofReal_comp).deriv

@[simp] theorem test_partialYY (x y : ℝ) :
    partialY (partialY testCoordinates) x y = (deriv (deriv cuspBump) y : ℂ) := by
  unfold partialY
  simp only [test_partialY]
  exact ((differentiable_deriv y).hasDerivAt.ofReal_comp).deriv

theorem printedL_test (z : ℍ) :
    printedL testCoordinates z = ((z.im : ℂ) ^ 2) * (deriv (deriv cuspBump) z.im : ℂ) := by
  have hx : partialX testCoordinates = 0 := by
    funext x y
    exact test_partialX x y
  rw [printedL, maassDelta, hx, test_partialYY]
  simp [partialX]

theorem printedL_test_density (z : ℍ) :
    (printedL testCoordinates z * (starRingEnd ℂ) (testCoordinates z.re z.im)).re / z.im ^ 2 =
      deriv (deriv cuspBump) z.im * cuspBump z.im := by
  rw [printedL_test, testCoordinates]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp [z.im_ne_zero]

private theorem derivative_square_integral_pos :
    0 < ∫ y : ℝ in (1 : ℝ)..6, deriv cuspBump y ^ 2 := by
  apply intervalIntegral.integral_pos (by norm_num : (1 : ℝ) < 6)
    (contDiff_deriv.continuous.pow 2).continuousOn
  · intro y _
    exact sq_nonneg _
  · by_contra! h
    have hzero : (∫ y : ℝ in (2 : ℝ)..3, deriv cuspBump y) = 0 := by
      calc
        _ = ∫ _ : ℝ in (2 : ℝ)..3, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)]
          intro y hy
          have hn := h y ⟨by linarith [hy.1], by linarith [hy.2]⟩
          have hsq := sq_nonneg (deriv cuspBump y)
          nlinarith
        _ = _ := by simp
    have hc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => (differentiable_bump y).hasDerivAt)
      (contDiff_deriv.continuous.intervalIntegrable 2 3)
    rw [hzero, cuspBump_one_on_middle (y := 3) (by norm_num) (by norm_num),
      cuspBump_zero_of_height_outside (y := 2) (Or.inl le_rfl), sub_zero] at hc
    norm_num at hc

theorem compact_cusp_test_negative :
    2 * (∫ y : ℝ in (1 : ℝ)..6, deriv (deriv cuspBump) y * cuspBump y) < 0 := by
  have hD := contDiff_deriv.continuous
  have hD₂ := contDiff_deriv.continuous_deriv_one
  have hB := cuspBump_smooth.continuous
  have h := intervalIntegral.integral_deriv_mul_eq_sub
    (fun y _ => (differentiable_deriv y).hasDerivAt)
    (fun y _ => (differentiable_bump y).hasDerivAt)
    (hD₂.intervalIntegrable 1 6) (hD.intervalIntegrable 1 6)
  rw [intervalIntegral.integral_add ((hD₂.mul hB).intervalIntegrable 1 6)
    ((hD.mul hD).intervalIntegrable 1 6),
    cuspBump_zero_of_height_outside (y := 6) (Or.inr (by norm_num)),
    cuspBump_zero_of_height_outside (y := 1) (Or.inl (by norm_num))] at h
  simp only [mul_zero, sub_zero] at h
  have hpos := derivative_square_integral_pos
  simp only [pow_two] at hpos
  linarith

end
end ManuscriptAudit.Paper9CuspLaplacianTest

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspLaplacianTest.printedL_test,
      ``ManuscriptAudit.Paper9CuspLaplacianTest.printedL_test_density,
      ``ManuscriptAudit.Paper9CuspLaplacianTest.compact_cusp_test_negative] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
