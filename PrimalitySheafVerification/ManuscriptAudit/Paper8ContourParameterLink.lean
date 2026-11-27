import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourDifference

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

end
end ManuscriptAudit.Paper8ContourParameterLink

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourParameterLink.fixed_phi_at_manuscript_nome,
      ``ManuscriptAudit.Paper8ContourParameterLink.positive_real_nome_has_upper_half_plane_parameter] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
