import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourDifference

/-! Fixed-circle uniform decay and at-zero continuity bounds for the literal contour difference. -/

namespace ManuscriptAudit.Paper8FixedContourDifferenceBounds

open Metric Set
open Paper8ContourSignedDominance (decay decay_nonneg)
open Paper8ContourGammaRemainder (bound bound_nonneg remainder remainder_norm_le)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos regular regular_norm_le_four
  regular_difference_norm_le)
open Paper8FixedContourDifference (difference regularDifference difference_eq_remainder_circleIntegral
  remainderDifference_integrable)
open Paper8HolomorphicPartPhase (periodCoefficient)

noncomputable section

private theorem sphere_norm {s : ℂ} (hs : s ∈ sphere (0 : ℂ) fixedRadius) :
    ‖s‖ = fixedRadius := by simpa only [mem_sphere, dist_zero_right] using hs

private theorem regularDifference_norm_le {ζ q s : ℂ} (hζ : ‖ζ‖ = 1)
    (hq : ‖q‖ ≤ 1 / 4) (hs : ‖s‖ ≤ fixedRadius) : ‖regularDifference ζ q s‖ ≤ 8 := by
  unfold regularDifference
  refine (norm_sub_le _ _).trans ?_
  have hR := regular_norm_le_four (α := 23) (β := 24) (by norm_num) (by norm_num)
    (by norm_num) le_rfl hζ hq hs
  have hL := regular_norm_le_four (α := 2 / 3) (β := 16) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hζ hq hs
  linarith

private theorem regularDifference_sub_zero_norm_le {ζ q s : ℂ} (hζ : ‖ζ‖ = 1)
    (hq : ‖q‖ ≤ 1 / 4) (hs : ‖s‖ ≤ fixedRadius) :
    ‖regularDifference ζ q s - regularDifference ζ 0 s‖ ≤ 16 * ‖q‖ := by
  have hEq : regularDifference ζ q s - regularDifference ζ 0 s =
      (regular 23 24 ζ q s - regular 23 24 ζ 0 s) -
        (regular (2 / 3) 16 ζ q s - regular (2 / 3) 16 ζ 0 s) := by
    unfold regularDifference
    ring
  rw [hEq]
  refine (norm_sub_le _ _).trans ?_
  have hR := regular_difference_norm_le (α := 23) (β := 24) (by norm_num) (by norm_num)
    (by norm_num) le_rfl hζ hq hs
  have hL := regular_difference_norm_le (α := 2 / 3) (β := 16) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hζ hq hs
  linarith

theorem difference_norm_le {k : ℕ} (hk : 0 < k) {ζ q : ℂ}
    (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    ‖difference k ζ q‖ ≤ (8 * fixedRadius * bound fixedRadius) * decay k := by
  rw [difference_eq_remainder_circleIntegral hk hζ hq]
  calc
    _ ≤ fixedRadius * ((decay k * bound fixedRadius) * 8) := by
      change ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        circleIntegral (fun s => remainder k s * regularDifference ζ q s) 0 fixedRadius‖ ≤ _
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const fixedRadius_pos.le
      intro s hs
      have h := sphere_norm hs
      rw [norm_mul]
      exact mul_le_mul (remainder_norm_le hk fixedRadius_pos h.ge)
        (regularDifference_norm_le hζ hq h.le) (norm_nonneg _)
        (mul_nonneg (decay_nonneg k) (bound_nonneg fixedRadius_pos))
    _ = _ := by ring

theorem difference_sub_zero_norm_le {k : ℕ} (hk : 0 < k) {ζ q : ℂ}
    (hζ : ‖ζ‖ = 1) (hq : ‖q‖ ≤ 1 / 4) :
    ‖difference k ζ q - difference k ζ 0‖ ≤ (16 * fixedRadius * bound fixedRadius) * decay k * ‖q‖ := by
  have hq₀ : ‖(0 : ℂ)‖ ≤ 1 / 4 := by norm_num
  rw [difference_eq_remainder_circleIntegral hk hζ hq,
    difference_eq_remainder_circleIntegral hk hζ hq₀, ← mul_sub,
    ← circleIntegral.integral_sub (remainderDifference_integrable hk hζ hq)
      (remainderDifference_integrable hk hζ hq₀)]
  calc
    _ ≤ fixedRadius * ((decay k * bound fixedRadius) * (16 * ‖q‖)) := by
      change ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ • circleIntegral (fun s =>
        remainder k s * regularDifference ζ q s -
          remainder k s * regularDifference ζ 0 s) 0 fixedRadius‖ ≤ _
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const fixedRadius_pos.le
      intro s hs
      have h := sphere_norm hs
      rw [← mul_sub, norm_mul]
      exact mul_le_mul (remainder_norm_le hk fixedRadius_pos h.ge)
        (regularDifference_sub_zero_norm_le hζ hq h.le) (norm_nonneg _)
        (mul_nonneg (decay_nonneg k) (bound_nonneg fixedRadius_pos))
    _ = _ := by ring

end
end ManuscriptAudit.Paper8FixedContourDifferenceBounds

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8FixedContourDifferenceBounds.difference_norm_le,
      ``ManuscriptAudit.Paper8FixedContourDifferenceBounds.difference_sub_zero_norm_le] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
