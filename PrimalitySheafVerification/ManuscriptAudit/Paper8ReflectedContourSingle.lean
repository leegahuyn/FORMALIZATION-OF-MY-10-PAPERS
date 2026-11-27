import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourSingle
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReflectedContourParameter

/-! A single reflected contour is its common m = 0 term plus an absolutely bounded tail. -/

namespace ManuscriptAudit.Paper8ReflectedContourSingle

open Metric Set
open Paper8ContourGammaSeries (a term coefficient)
open Paper8ContourGammaRemainder (bound bound_nonneg remainder remainder_norm_le a_eq_first_add_remainder)
open Paper8ContourSignedDominance (decay decay_nonneg)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos regular regular_s_zero)
open Paper8ReflectedContourParameter (reflected_differentiableOn reflected_norm_le_four)
open Paper8FixedContourSingle (common singleRemainder)
open Paper8FixedContourDifference (phiAtQ sphere_point_ne_zero first_continuousOn remainder_continuousOn)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8ContourMomentTerm (periodCoefficient_ne_zero)

noncomputable section

private theorem first_circleIntegral (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    (k : ℕ) {ζ q : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    circleIntegral (fun s => term k 0 s * regular (-α) (-β) ζ q s) 0 fixedRadius =
      periodCoefficient * common k ζ q := by
  have hC := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul fixedRadius_pos 0
    (reflected_differentiableOn α hβ hβ' hζ hq)
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, iteratedDeriv_zero, regular_s_zero] at hC
  have hFun : (fun s => term k 0 s * regular (-α) (-β) ζ q s) =
      (fun s : ℂ => (coefficient k 0 : ℂ) * ((1 / (s - 0) ^ (0 + 1 : ℕ)) • regular (-α) (-β) ζ q s)) := by
    funext s
    simp only [term, sub_zero, smul_eq_mul, div_eq_mul_inv, one_mul, mul_assoc]
  rw [hFun, circleIntegral.integral_const_mul, hC, common, periodCoefficient]
  ring

theorem phi_eq_common_add_remainder (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24)
    {k : ℕ} (hk : 0 < k) {ζ q : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    phiAtQ (-α) (-β) k ζ q = common k ζ q + singleRemainder (-α) (-β) k ζ q := by
  have hCont : ContinuousOn (regular (-α) (-β) ζ q) (sphere (0 : ℂ) fixedRadius) :=
    (reflected_differentiableOn α hβ hβ' hζ hq).continuousOn.mono sphere_subset_closedBall
  have hFirst : CircleIntegrable (fun s => term k 0 s * regular (-α) (-β) ζ q s) 0 fixedRadius :=
    ((first_continuousOn k).mul hCont).circleIntegrable fixedRadius_pos.le
  have hTail : CircleIntegrable (fun s => remainder k s * regular (-α) (-β) ζ q s) 0 fixedRadius :=
    ((remainder_continuousOn hk).mul hCont).circleIntegrable fixedRadius_pos.le
  unfold phiAtQ singleRemainder
  have hEq :
      circleIntegral (fun s => a k s * regular (-α) (-β) ζ q s) 0 fixedRadius =
        circleIntegral (fun s => term k 0 s * regular (-α) (-β) ζ q s +
          remainder k s * regular (-α) (-β) ζ q s) 0 fixedRadius := by
    apply circleIntegral.integral_congr fixedRadius_pos.le
    intro s hs
    change a k s * regular (-α) (-β) ζ q s = term k 0 s * regular (-α) (-β) ζ q s +
      remainder k s * regular (-α) (-β) ζ q s
    rw [a_eq_first_add_remainder hk (sphere_point_ne_zero hs), add_mul]
  have hAdd : circleIntegral (fun s => term k 0 s * regular (-α) (-β) ζ q s +
        remainder k s * regular (-α) (-β) ζ q s) 0 fixedRadius =
      circleIntegral (fun s => term k 0 s * regular (-α) (-β) ζ q s) 0 fixedRadius +
        circleIntegral (fun s => remainder k s * regular (-α) (-β) ζ q s) 0 fixedRadius :=
    circleIntegral.integral_add hFirst hTail
  rw [hEq, hAdd,
    first_circleIntegral α hβ hβ' k hζ hq, mul_add,
    ← mul_assoc periodCoefficient⁻¹ periodCoefficient,
    inv_mul_cancel₀ periodCoefficient_ne_zero, one_mul]

theorem singleRemainder_norm_le {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) {k : ℕ} (hk : 0 < k) {ζ q : ℂ}
    (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    ‖singleRemainder (-α) (-β) k ζ q‖ ≤ (4 * fixedRadius * bound fixedRadius) * decay k := by
  unfold singleRemainder
  calc
    _ ≤ fixedRadius * ((decay k * bound fixedRadius) * 4) := by
      change ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        circleIntegral (fun s => remainder k s * regular (-α) (-β) ζ q s) 0 fixedRadius‖ ≤ _
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const fixedRadius_pos.le
      intro s hs
      have h : ‖s‖ = fixedRadius := by simpa only [mem_sphere, dist_zero_right] using hs
      rw [norm_mul]
      exact mul_le_mul (remainder_norm_le hk fixedRadius_pos h.ge)
        (reflected_norm_le_four hα hα' hβ hβ' hζ hq h.le) (norm_nonneg _)
        (mul_nonneg (decay_nonneg k) (bound_nonneg fixedRadius_pos))
    _ = _ := by ring

end
end ManuscriptAudit.Paper8ReflectedContourSingle

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReflectedContourSingle.phi_eq_common_add_remainder,
      ``ManuscriptAudit.Paper8ReflectedContourSingle.singleRemainder_norm_le] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
