import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourParameterLink
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalContour

/-! The actual lower-half-plane local contour at its small radius equals the fixed inverse-nome kernel. -/

namespace ManuscriptAudit.Paper8LowerContourParameterLink

open Metric Set
open Paper8HolomorphicPartPhase (periodCoefficient qParameter qParameter_norm)
open Paper8LocalContour (root radius phi integrand radius_pos root_norm)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos)
open Paper8FixedContourDifference (phiAtQ)
open Paper8ContourParameterLink (fixed_phi_at_manuscript_nome)
open Paper8ReciprocalContour (integrand_reciprocal)
open Paper8ContourRadius (circleIntegral_eq_of_small_radii)

noncomputable section

private theorem fixedRadius_le_lower_radius {z : ℂ} (hz : z.im < 0)
    (hq : ‖qParameter (-z)‖ ≤ 1 / 4) : fixedRadius ≤ radius z := by
  have hQuarter : (1 / 4 : ℝ) = Real.exp (-(2 * Real.log 2)) := by
    rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [qParameter_norm, Complex.neg_im, hQuarter] at hq
  have h := Real.exp_le_exp.mp hq
  have hHeight : Real.log 2 ≤ Real.pi * |z.im| := by rw [abs_of_neg hz]; linarith
  exact div_le_div_of_nonneg_right hHeight (by norm_num)

theorem scaled_phi_eq_inverse_nome (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    {k : ℕ} (hk : 0 < k) (d : ℤ) {z : ℂ} (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4) :
    (root k ^ d * qParameter z) * phi α β k d z =
      -phiAtQ (α - β) (-β) k (root k ^ d)⁻¹ (qParameter (-z)) := by
  have hLe := fixedRadius_le_lower_radius hz hq
  have hSafe : β * radius z < 2 * Real.pi * |z.im| := by
    calc
      _ ≤ 24 * radius z := mul_le_mul_of_nonneg_right hβ' (radius_pos hz.ne).le
      _ = Real.pi * |z.im| := by unfold radius; ring
      _ < _ := by linarith [mul_pos Real.pi_pos (abs_pos.mpr hz.ne)]
  rw [phi, circleIntegral_eq_of_small_radii hk d α hβ fixedRadius_pos hLe hSafe, ← zpow_neg,
    fixed_phi_at_manuscript_nome (α - β) (-β) k (-d) (-z)]
  calc
    _ = periodCoefficient⁻¹ * circleIntegral
        (fun s => (root k ^ d * qParameter z) * integrand α β k d z s) 0 fixedRadius := by
      rw [circleIntegral.integral_const_mul]
      ring
    _ = periodCoefficient⁻¹ * circleIntegral
        (fun s => (-1 : ℂ) * integrand (α - β) (-β) k (-d) (-z) s) 0 fixedRadius := by
      apply congrArg (fun w : ℂ => periodCoefficient⁻¹ * w)
      apply circleIntegral.integral_congr fixedRadius_pos.le
      intro s hs
      have hN : ‖s‖ = fixedRadius := by simpa only [mem_sphere, dist_zero_right] using hs
      have hP : β * ‖s‖ < 2 * Real.pi * |z.im| := by
        rw [hN]
        exact (mul_le_mul_of_nonneg_left hLe hβ.le).trans_lt hSafe
      simpa only [neg_one_mul] using integrand_reciprocal α hβ k d hP
    _ = _ := by rw [circleIntegral.integral_const_mul]; ring

theorem nome_mul_phi_eq_inverse_nome (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    {k : ℕ} (hk : 0 < k) (d : ℤ) {z : ℂ} (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4) :
    qParameter z * phi α β k d z =
      -(root k ^ d)⁻¹ * phiAtQ (α - β) (-β) k (root k ^ d)⁻¹ (qParameter (-z)) := by
  have hN : ‖root k ^ d‖ = 1 := by rw [norm_zpow, root_norm, one_zpow]
  have hNZ : root k ^ d ≠ 0 := by
    intro h
    rw [h, norm_zero] at hN
    norm_num at hN
  calc
    _ = (root k ^ d)⁻¹ * ((root k ^ d * qParameter z) * phi α β k d z) := by
      field_simp [hNZ] <;> ring
    _ = _ := by rw [scaled_phi_eq_inverse_nome α hβ hβ' hk d hz hq]; ring

end
end ManuscriptAudit.Paper8LowerContourParameterLink

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8LowerContourParameterLink.scaled_phi_eq_inverse_nome,
      ``ManuscriptAudit.Paper8LowerContourParameterLink.nome_mul_phi_eq_inverse_nome] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
