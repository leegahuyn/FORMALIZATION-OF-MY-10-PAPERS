import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourDifference
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReflectedContourParameter

/-! Cancellation of the shared m=0 term for the actual inverse-nome kernels. -/

namespace ManuscriptAudit.Paper8ReflectedContourDifference

open Metric Set
open Paper8ContourGammaSeries (a term coefficient differentiableOn_punctured)
open Paper8ContourGammaRemainder (remainder a_eq_first_add_remainder)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos regular regular_s_zero)
open Paper8ReflectedContourParameter (reflected_differentiableOn)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8FixedContourDifference (phiAtQ sphere_point_ne_zero first_continuousOn remainder_continuousOn)

noncomputable section

def regularDifference (ζ q s : ℂ) : ℂ :=
  regular (-1) (-24) ζ q s - regular (-(46 / 3)) (-16) ζ q s

def difference (k : ℕ) (ζ q : ℂ) : ℂ :=
  phiAtQ (-1) (-24) k ζ q - phiAtQ (-(46 / 3)) (-16) k ζ q

private theorem a_continuousOn {k : ℕ} (hk : 0 < k) :
    ContinuousOn (a k) (sphere (0 : ℂ) fixedRadius) :=
  (differentiableOn_punctured hk).continuousOn.mono (fun _ hs => sphere_point_ne_zero hs)

theorem regularDifference_continuousOn {ζ q : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    ContinuousOn (regularDifference ζ q) (sphere (0 : ℂ) fixedRadius) :=
  ((reflected_differentiableOn 1 (β := 24) (by norm_num) le_rfl hζ hq).continuousOn.mono
    sphere_subset_closedBall).sub
      ((reflected_differentiableOn (46 / 3) (β := 16) (by norm_num) (by norm_num) hζ hq).continuousOn.mono
        sphere_subset_closedBall)

theorem remainderDifference_integrable {k : ℕ} (hk : 0 < k) {ζ q : ℂ}
    (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    CircleIntegrable (fun s => remainder k s * regularDifference ζ q s) 0 fixedRadius :=
  ((remainder_continuousOn hk).mul (regularDifference_continuousOn hζ hq)).circleIntegrable
    fixedRadius_pos.le

private theorem first_circle_cancel_eq_zero (k : ℕ) {ζ q : ℂ} (hζ : ‖ζ‖ = 1)
    (hq : ‖q‖ ≤ 1 / 4) :
    circleIntegral (fun s => term k 0 s * regularDifference ζ q s) 0 fixedRadius = 0 := by
  have hd : DifferentiableOn ℂ (regularDifference ζ q) (closedBall (0 : ℂ) fixedRadius) :=
    (reflected_differentiableOn 1 (β := 24) (by norm_num) le_rfl hζ hq).sub
      (reflected_differentiableOn (46 / 3) (β := 16) (by norm_num) (by norm_num) hζ hq)
  have h0 : regularDifference ζ q 0 = 0 := by simp [regularDifference, regular_s_zero]
  have hC := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul fixedRadius_pos 0 hd
  simp only [iteratedDeriv_zero, h0, smul_zero] at hC
  have hFun : (fun s => term k 0 s * regularDifference ζ q s) =
      (fun s : ℂ => (coefficient k 0 : ℂ) * ((1 / (s - 0) ^ (0 + 1 : ℕ)) • regularDifference ζ q s)) := by
    funext s
    simp only [term, sub_zero, smul_eq_mul, div_eq_mul_inv, one_mul, mul_assoc]
  rw [hFun, circleIntegral.integral_const_mul, hC, mul_zero]

theorem difference_eq_remainder_circleIntegral {k : ℕ} (hk : 0 < k) {ζ q : ℂ}
    (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    difference k ζ q = periodCoefficient⁻¹ *
      circleIntegral (fun s => remainder k s * regularDifference ζ q s) 0 fixedRadius := by
  have hCont (α : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 24) :
      ContinuousOn (fun s => a k s * regular (-α) (-β) ζ q s) (sphere (0 : ℂ) fixedRadius) :=
    (a_continuousOn hk).mul ((reflected_differentiableOn α hβ hβ' hζ hq).continuousOn.mono
      sphere_subset_closedBall)
  have hR := (hCont 1 (β := 24) (by norm_num) le_rfl).circleIntegrable fixedRadius_pos.le
  have hL := (hCont (46 / 3) (β := 16) (by norm_num) (by norm_num)).circleIntegrable fixedRadius_pos.le
  unfold difference phiAtQ
  rw [← mul_sub, ← circleIntegral.integral_sub hR hL]
  congr 1
  have hTerm : CircleIntegrable (fun s => term k 0 s * regularDifference ζ q s) 0 fixedRadius :=
    ((first_continuousOn k).mul (regularDifference_continuousOn hζ hq)).circleIntegrable fixedRadius_pos.le
  calc
    _ = circleIntegral (fun s => term k 0 s * regularDifference ζ q s +
          remainder k s * regularDifference ζ q s) 0 fixedRadius := by
      apply circleIntegral.integral_congr fixedRadius_pos.le
      intro s hs
      change a k s * regular (-1) (-24) ζ q s - a k s * regular (-(46 / 3)) (-16) ζ q s =
        term k 0 s * regularDifference ζ q s + remainder k s * regularDifference ζ q s
      rw [a_eq_first_add_remainder hk (sphere_point_ne_zero hs)]
      unfold regularDifference
      ring
    _ = circleIntegral (fun s => term k 0 s * regularDifference ζ q s) 0 fixedRadius +
          circleIntegral (fun s => remainder k s * regularDifference ζ q s) 0 fixedRadius :=
      circleIntegral.integral_add hTerm (remainderDifference_integrable hk hζ hq)
    _ = _ := by rw [first_circle_cancel_eq_zero k hζ hq, zero_add]

end
end ManuscriptAudit.Paper8ReflectedContourDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReflectedContourDifference.remainderDifference_integrable,
      ``ManuscriptAudit.Paper8ReflectedContourDifference.difference_eq_remainder_circleIntegral] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
