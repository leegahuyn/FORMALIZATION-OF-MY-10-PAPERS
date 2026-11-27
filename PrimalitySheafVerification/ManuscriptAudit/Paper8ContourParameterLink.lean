import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourDifference
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourRadius

/-! The fixed-radius integrals use the literal manuscript integrands and nome. -/

namespace ManuscriptAudit.Paper8ContourParameterLink

open Paper8FixedContourDifference (phiAtQ)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos regular denominator factor)
open Paper8LocalContour (root integrand)
open Paper8HolomorphicPartPhase (qParameter periodCoefficient)

noncomputable section

theorem fixed_phi_at_manuscript_nome (α β : ℝ) (k : ℕ) (d : ℤ) (z : ℂ) :
    phiAtQ α β k (root k ^ d) (qParameter z) =
      periodCoefficient⁻¹ * circleIntegral (integrand α β k d z) 0 fixedRadius := by
  unfold phiAtQ
  apply congrArg (fun w : ℂ => periodCoefficient⁻¹ * w)
  apply circleIntegral.integral_congr fixedRadius_pos.le
  intro s _
  unfold integrand regular denominator factor Paper8LocalContour.denominator Paper8LocalContour.factor
  rw [mul_div_assoc]

theorem positive_real_nome_has_upper_half_plane_parameter {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    ∃ z : ℂ, 0 < z.im ∧ qParameter z = (q : ℂ) := by
  let y : ℝ := -Real.log q / (2 * Real.pi)
  let z : ℂ := (y : ℂ) * Complex.I
  have hY : 0 < y := by
    exact div_pos (neg_pos.mpr (Real.log_neg hq h₁)) (mul_pos (by norm_num) Real.pi_pos)
  have hZ : 0 < z.im := by simpa [z, Complex.mul_im] using hY
  have hLog : -(2 * Real.pi * y) = Real.log q := by
    unfold y
    field_simp [Real.pi_ne_zero] <;> ring
  have hArg : periodCoefficient * z = ((-(2 * Real.pi * y) : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * Complex.I ^ 2 := by
        unfold periodCoefficient z
        ring
      _ = _ := by rw [Complex.I_sq]; ring
  refine ⟨z, hZ, ?_⟩
  rw [qParameter, hArg, ← Complex.ofReal_exp, hLog, Real.exp_log hq]

private theorem log_two_le_height {z : ℂ} (hq : ‖qParameter z‖ ≤ 1 / 4) :
    Real.log 2 ≤ Real.pi * z.im := by
  have hQuarter : (1 / 4 : ℝ) = Real.exp (-(2 * Real.log 2)) := by
    rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [Paper8HolomorphicPartPhase.qParameter_norm, hQuarter] at hq
  have h := Real.exp_le_exp.mp hq
  linarith

theorem fixed_phi_eq_local_small_radius_phi (α : ℝ) {β : ℝ} (hβ : 0 < β) (hβ' : β ≤ 24)
    {k : ℕ} (hk : 0 < k) (d : ℤ) {z : ℂ} (hq : ‖qParameter z‖ ≤ 1 / 4) :
    phiAtQ α β k (root k ^ d) (qParameter z) = Paper8LocalContour.phi α β k d z := by
  have hLog := log_two_le_height hq
  have hIm : 0 < z.im := by
    by_contra! h
    have hh := mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le h
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hRadius : fixedRadius ≤ Paper8LocalContour.radius z := by
    unfold fixedRadius Paper8LocalContour.radius
    rw [abs_of_pos hIm]
    exact div_le_div_of_nonneg_right hLog (by norm_num)
  have hSafe : β * Paper8LocalContour.radius z < 2 * Real.pi * |z.im| := by
    calc
      _ ≤ 24 * Paper8LocalContour.radius z :=
        mul_le_mul_of_nonneg_right hβ' (Paper8LocalContour.radius_pos hIm.ne').le
      _ = Real.pi * |z.im| := by unfold Paper8LocalContour.radius; ring
      _ < _ := by linarith [mul_pos Real.pi_pos (abs_pos.mpr hIm.ne')]
  rw [fixed_phi_at_manuscript_nome, Paper8LocalContour.phi]
  exact congrArg (fun w : ℂ => periodCoefficient⁻¹ * w)
    (Paper8ContourRadius.circleIntegral_eq_of_small_radii hk d α hβ fixedRadius_pos hRadius hSafe).symm

end
end ManuscriptAudit.Paper8ContourParameterLink

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourParameterLink.fixed_phi_at_manuscript_nome,
      ``ManuscriptAudit.Paper8ContourParameterLink.positive_real_nome_has_upper_half_plane_parameter,
      ``ManuscriptAudit.Paper8ContourParameterLink.fixed_phi_eq_local_small_radius_phi] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
