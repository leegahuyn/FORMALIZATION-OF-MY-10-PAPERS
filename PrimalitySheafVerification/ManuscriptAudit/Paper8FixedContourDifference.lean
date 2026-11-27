import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourParameter
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourGammaRemainder

/-! The exact common m = 0 contour term cancels on the fixed small q-disk. -/

namespace ManuscriptAudit.Paper8FixedContourDifference

open Metric Set
open Paper8ContourGammaSeries (a term coefficient differentiableOn_punctured)
open Paper8ContourGammaRemainder (remainder a_eq_first_add_remainder)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos regular regular_at_zero regular_s_zero
  regular_differentiableOn)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8ContourMoment (atZero atZero_eq_its_real_part)
open Paper8ContourCoefficientDecay (delta delta_eq_moments)

noncomputable section

def phiAtQ (α β : ℝ) (k : ℕ) (ζ q : ℂ) : ℂ :=
  periodCoefficient⁻¹ * circleIntegral (fun s => a k s * regular α β ζ q s) 0 fixedRadius

def regularDifference (ζ q s : ℂ) : ℂ := regular 23 24 ζ q s - regular (2 / 3) 16 ζ q s

def difference (k : ℕ) (ζ q : ℂ) : ℂ := phiAtQ 23 24 k ζ q - phiAtQ (2 / 3) 16 k ζ q

theorem sphere_point_ne_zero {s : ℂ} (hs : s ∈ sphere (0 : ℂ) fixedRadius) : s ≠ 0 := by
  have h : ‖s‖ = fixedRadius := by simpa only [mem_sphere, dist_zero_right] using hs
  exact norm_pos_iff.mp (by simpa only [h] using fixedRadius_pos)

private theorem a_continuousOn {k : ℕ} (hk : 0 < k) :
    ContinuousOn (a k) (sphere (0 : ℂ) fixedRadius) :=
  (differentiableOn_punctured hk).continuousOn.mono (fun _ hs => sphere_point_ne_zero hs)

theorem first_continuousOn (k : ℕ) :
    ContinuousOn (term k 0) (sphere (0 : ℂ) fixedRadius) := by
  have h : ContinuousOn (fun s : ℂ => (coefficient k 0 : ℂ) / s)
      (sphere (0 : ℂ) fixedRadius) :=
    continuousOn_const.div continuous_id.continuousOn (fun _ hs => sphere_point_ne_zero hs)
  change ContinuousOn (fun s : ℂ => (coefficient k 0 : ℂ) / s ^ (0 + 1 : ℕ))
    (sphere (0 : ℂ) fixedRadius)
  simpa only [zero_add, pow_one] using h

theorem remainder_continuousOn {k : ℕ} (hk : 0 < k) :
    ContinuousOn (remainder k) (sphere (0 : ℂ) fixedRadius) := by
  have h := (a_continuousOn hk).sub (first_continuousOn k)
  refine h.congr fun s hs => ?_
  change remainder k s = a k s - term k 0 s
  rw [a_eq_first_add_remainder hk (sphere_point_ne_zero hs)]
  ring

theorem regularDifference_continuousOn {ζ q : ℂ} (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    ContinuousOn (regularDifference ζ q) (sphere (0 : ℂ) fixedRadius) :=
  ((regular_differentiableOn 23 (β := 24) (by norm_num) le_rfl hζ hq).continuousOn.mono
    sphere_subset_closedBall).sub
      ((regular_differentiableOn (2 / 3) (β := 16) (by norm_num) (by norm_num) hζ hq).continuousOn.mono
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
    (regular_differentiableOn 23 (β := 24) (by norm_num) le_rfl hζ hq).sub
      (regular_differentiableOn (2 / 3) (β := 16) (by norm_num) (by norm_num) hζ hq)
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
      ContinuousOn (fun s => a k s * regular α β ζ q s) (sphere (0 : ℂ) fixedRadius) :=
    (a_continuousOn hk).mul ((regular_differentiableOn α hβ hβ' hζ hq).continuousOn.mono
      sphere_subset_closedBall)
  have hR := (hCont 23 (β := 24) (by norm_num) le_rfl).circleIntegrable fixedRadius_pos.le
  have hL := (hCont (2 / 3) (β := 16) (by norm_num) (by norm_num)).circleIntegrable fixedRadius_pos.le
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
      change a k s * regular 23 24 ζ q s - a k s * regular (2 / 3) 16 ζ q s =
        term k 0 s * regularDifference ζ q s + remainder k s * regularDifference ζ q s
      rw [a_eq_first_add_remainder hk (sphere_point_ne_zero hs)]
      unfold regularDifference
      ring
    _ = circleIntegral (fun s => term k 0 s * regularDifference ζ q s) 0 fixedRadius +
          circleIntegral (fun s => remainder k s * regularDifference ζ q s) 0 fixedRadius :=
      circleIntegral.integral_add hTerm (remainderDifference_integrable hk hζ hq)
    _ = _ := by rw [first_circle_cancel_eq_zero k hζ hq, zero_add]

private theorem phiAtQ_zero (α β : ℝ) (k : ℕ) (ζ : ℂ) :
    phiAtQ α β k ζ 0 = atZero α k fixedRadius := by
  simp only [phiAtQ, atZero, regular_at_zero]

theorem difference_at_zero {k : ℕ} (hk : 0 < k) (ζ : ℂ) :
    difference k ζ 0 = (delta k : ℂ) := by
  rw [difference, phiAtQ_zero 23 24, phiAtQ_zero (2 / 3) 16,
    atZero_eq_its_real_part hk 23 fixedRadius_pos, atZero_eq_its_real_part hk (2 / 3) fixedRadius_pos,
    ← Complex.ofReal_sub, ← delta_eq_moments hk fixedRadius_pos]

end
end ManuscriptAudit.Paper8FixedContourDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8FixedContourDifference.remainderDifference_integrable,
      ``ManuscriptAudit.Paper8FixedContourDifference.difference_eq_remainder_circleIntegral,
      ``ManuscriptAudit.Paper8FixedContourDifference.difference_at_zero] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
