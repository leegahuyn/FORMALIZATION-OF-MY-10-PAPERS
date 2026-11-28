import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombDirichletWeak

/-! Unrestricted weak gradient tests detect the boundary of the actual
width-two Dirichlet residual. -/

namespace ManuscriptAudit.Paper10CoulombBoundaryFlux

open MeasureTheory
open Paper10CoulombDirichletMode (v v_smooth residual)
open Paper10CoulombDirichletWeak (weakPair)
open Paper10CoulombMultiplier (ScalarField)
open SmoothGaugeCurvature (partialX partialY)
open scoped ContDiff Interval

noncomputable section

def testPotential : ScalarField := fun x y ↦ Real.sin (Real.pi * x) * v y

theorem test_smooth : ContDiff ℝ ∞ (Function.uncurry testPotential) :=
  (Real.contDiff_sin.comp (contDiff_const.mul contDiff_fst)).mul (v_smooth.comp contDiff_snd)

theorem test_periodic (x y : ℝ) (k : ℤ) :
    testPotential (x + 2 * (k : ℝ)) y = testPotential x y := by
  unfold testPotential
  rw [show Real.pi * (x + 2 * (k : ℝ)) =
    Real.pi * x + (k : ℝ) * (2 * Real.pi) by ring, Real.sin_add_int_mul_two_pi]

private theorem partial_x (x y : ℝ) :
    partialX testPotential x y = Real.cos (Real.pi * x) * Real.pi * v y := by
  have hx := ((Real.hasDerivAt_sin (Real.pi * x)).comp x
    ((hasDerivAt_id x).const_mul Real.pi)).mul_const (v y)
  change deriv (fun z ↦ Real.sin (Real.pi * z) * v y) x = _
  simpa using hx.deriv

private theorem partial_y (x y : ℝ) :
    partialY testPotential x y = Real.sin (Real.pi * x) * deriv v y :=
  (((v_smooth.differentiable (by simp) y).hasDerivAt).const_mul
    (Real.sin (Real.pi * x))).deriv

private theorem endpoint_four : v 4 = 0 := by
  have h := congrArg Prod.snd
    (Paper10CoulombDirichletMode.zero_below_cusp_band (1/2) 4 (by norm_num)).2.1
  change -(Real.sin (Real.pi * (1/2)) * v 4) = 0 at h
  rw [show Real.pi * (1/2) = Real.pi / 2 by ring, Real.sin_pi_div_two] at h
  simpa using h

private theorem endpoint_six : v 6 = 1 := by
  have h := Paper10CoulombDirichletMode.residual_nonzero_on_boundary
  change -(Real.sin (Real.pi * (1/2)) * v 6) = -1 at h
  rw [show Real.pi * (1/2) = Real.pi / 2 by ring, Real.sin_pi_div_two] at h
  simpa using h

private theorem vertical_integral :
    (∫ y : ℝ in 4..6, -(deriv v y * v y)) = -(1/2) := by
  have hd (y : ℝ) : HasDerivAt (fun z ↦ v z * v z / 2) (deriv v y * v y) y := by
    have h := (v_smooth.differentiable (by simp) y).hasDerivAt
    convert (h.mul h).div_const (2 : ℝ) using 1 <;> ring
  have hc : Continuous (fun y ↦ deriv v y * v y) :=
    (show ContDiff ℝ ∞ (deriv v) from ContDiff.deriv' (by simpa using v_smooth)).continuous.mul
      v_smooth.continuous
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ hd y)
      (hc.intervalIntegrable (μ := volume) _ _)]
  norm_num [endpoint_four, endpoint_six]

private theorem horizontal_width :
    (∫ x : ℝ in 0..2, Real.cos (Real.pi * x)^2) +
      (∫ x : ℝ in 0..2, Real.sin (Real.pi * x)^2) = 2 := by
  have hc : Continuous (fun x : ℝ ↦ Real.cos (Real.pi * x)^2) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2
  have hs : Continuous (fun x : ℝ ↦ Real.sin (Real.pi * x)^2) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2
  rw [← intervalIntegral.integral_add (hc.intervalIntegrable (μ := volume) _ _)
    (hs.intervalIntegrable (μ := volume) _ _)]
  have h : (fun x : ℝ ↦ Real.cos (Real.pi * x)^2 + Real.sin (Real.pi * x)^2) =
      fun _ ↦ (1:ℝ) := by
    funext x
    rw [add_comm, Real.sin_sq_add_cos_sq]
  change (∫ x : ℝ in 0..2, (fun x : ℝ ↦ Real.cos (Real.pi * x)^2 +
    Real.sin (Real.pi * x)^2) x) = _
  rw [h, intervalIntegral.integral_const]
  norm_num

/-- The same residual has nonzero weak pairing with a smooth periodic
gradient when the test potential may have nonzero boundary trace. -/
theorem unrestricted_weak_pair : weakPair testPotential = -1 := by
  change (∫ x : ℝ in 0..2, ∫ y : ℝ in 4..6,
      (residual x y).1 * partialX testPotential x y) +
    (∫ x : ℝ in 0..2, ∫ y : ℝ in 4..6,
      (residual x y).2 * partialY testPotential x y) = _
  have hx (x y : ℝ) :
      (residual x y).1 * partialX testPotential x y =
        Real.cos (Real.pi * x)^2 * (-(deriv v y * v y)) := by
    rw [partial_x]
    unfold residual
    dsimp
    field_simp [Real.pi_ne_zero] <;> ring
  have hy (x y : ℝ) :
      (residual x y).2 * partialY testPotential x y =
        Real.sin (Real.pi * x)^2 * (-(deriv v y * v y)) := by
    rw [partial_y]
    unfold residual
    dsimp
    ring
  simp_rw [hx, hy, intervalIntegral.integral_const_mul, vertical_integral,
    intervalIntegral.integral_mul_const]
  rw [← add_mul, horizontal_width]
  norm_num

end
end ManuscriptAudit.Paper10CoulombBoundaryFlux

open Lean Elab Command in
run_cmd do
  let names := [``ManuscriptAudit.Paper10CoulombBoundaryFlux.test_smooth,
    ``ManuscriptAudit.Paper10CoulombBoundaryFlux.test_periodic,
    ``ManuscriptAudit.Paper10CoulombBoundaryFlux.unrestricted_weak_pair]
  for name in names do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
