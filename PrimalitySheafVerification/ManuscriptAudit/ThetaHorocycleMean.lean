import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PrimalitySheafVerification.ManuscriptAudit.ThetaProfilesNonzero

/-! The standard weighted theta mode has a nonzero constant term at the infinity cusp. -/

namespace ManuscriptAudit.ThetaHorocycleMean

open MeasureTheory MaassLaplacian ThetaProfilesNonzero

noncomputable section

theorem theta_real_pos_at_height {τ : ℂ} (hτ : (2 / 3 : ℝ) < τ.im) :
    0 < (jacobiTheta τ).re := by
  have h := (Complex.abs_re_le_norm (jacobiTheta τ - 1)).trans_lt
    (jacobiTheta_sub_one_norm_lt_one_at_height hτ)
  rw [Complex.sub_re, Complex.one_re] at h
  linarith only [(abs_lt.mp h).1]

theorem thetaWeightedMode_horocycleMean_re_pos (y : ℝ) (hy : 2 / 3 < y) :
    0 < (∫ x : ℝ in (0 : ℝ)..2, weighted (1 / 4) jacobiTheta x y).re := by
  have hy' : 0 < y := by linarith
  have hZ : Continuous (fun x : ℝ => complexPoint x y) :=
    Complex.continuous_ofReal.add continuous_const
  have hF : Continuous (fun x : ℝ => jacobiTheta (complexPoint x y)) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have him : (complexPoint x y).im = y := by simp [complexPoint]
    exact ContinuousAt.comp' (f := fun x => complexPoint x y) (x := x)
      (continuousAt_jacobiTheta (him.symm ▸ hy')) hZ.continuousAt
  have hWF : Continuous (fun x : ℝ => weighted (1 / 4) jacobiTheta x y) :=
    continuous_const.mul hF
  have hWFI := hWF.intervalIntegrable (μ := (volume : Measure ℝ)) 0 2
  have hInt := (Complex.continuous_re.comp hWF).intervalIntegrable
    (μ := (volume : Measure ℝ)) 0 2
  let reL : ℂ →L[ℝ] ℝ := RCLike.reCLM
  have hRe := reL.intervalIntegral_comp_comm hWFI
  change (∫ x : ℝ in (0 : ℝ)..2, (weighted (1 / 4) jacobiTheta x y).re) =
    (∫ x : ℝ in (0 : ℝ)..2, weighted (1 / 4) jacobiTheta x y).re at hRe
  rw [← hRe]
  apply intervalIntegral.intervalIntegral_pos_of_pos hInt _ (by norm_num)
  intro x
  change 0 < (((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) * jacobiTheta (complexPoint x y)).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (Real.rpow_pos_of_pos hy' _)
    (theta_real_pos_at_height (by simpa [complexPoint] using hy))

theorem thetaWeightedMode_horocycleMean_ne_zero (y : ℝ) (hy : 2 / 3 < y) :
    (∫ x : ℝ in (0 : ℝ)..2, weighted (1 / 4) jacobiTheta x y) ≠ 0 := by
  intro h
  have hp := thetaWeightedMode_horocycleMean_re_pos y hy
  rw [h, Complex.zero_re] at hp
  exact (lt_irrefl _) hp

end
end ManuscriptAudit.ThetaHorocycleMean

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaHorocycleMean.theta_real_pos_at_height,
      ``ManuscriptAudit.ThetaHorocycleMean.thetaWeightedMode_horocycleMean_re_pos,
      ``ManuscriptAudit.ThetaHorocycleMean.thetaWeightedMode_horocycleMean_ne_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
