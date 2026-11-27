import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9ThetaUnitTranslate
import PrimalitySheafVerification.ManuscriptAudit.ThetaGammaTwoMetric
import PrimalitySheafVerification.ManuscriptAudit.ModularQRadius

/-!
# An actual Γ(2) theta density fails to factor through the printed q-coordinate

The two lifted points 2i and 1+2i have the same printed q. Their
genuine quotient theta densities are distinct, so even this specified
automorphic scalar cannot be represented as a function of that q.
This directly tests the scalar coordinate identification on pp. 440–441.
-/

namespace ManuscriptAudit.Paper9ThetaQCoordinate

open UpperHalfPlane
open LiteralCuspTruncation (orbitPoint)
open ModularQRadius (qParameter)
open Paper9ThetaUnitTranslate (axis translated_theta_norm_strictly_smaller)
open ThetaProfileGenerators (thetaDensity)
open ThetaGammaTwoMetric (quotientThetaDensity quotientThetaDensity_apply)

noncomputable section

theorem actual_theta_density_printed_q_collision :
    ∃ z w : ℍ, qParameter w = qParameter z ∧
      quotientThetaDensity (orbitPoint w) < quotientThetaDensity (orbitPoint z) := by
  let z : ℍ := ⟨axis 2, by norm_num [axis, Complex.mul_im]⟩
  let w : ℍ := ⟨axis 2 + 1, by norm_num [axis, Complex.add_im, Complex.mul_im]⟩
  have hIm : w.im = z.im := by simp [w, z, axis, Complex.add_im]
  refine ⟨z, w, ?_, ?_⟩
  · have hArg : 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) =
          2 * (Real.pi : ℂ) * Complex.I * (z : ℂ) + 2 * (Real.pi : ℂ) * Complex.I := by
      change 2 * (Real.pi : ℂ) * Complex.I * (axis 2 + 1) = _
      change _ = 2 * (Real.pi : ℂ) * Complex.I * axis 2 + 2 * (Real.pi : ℂ) * Complex.I
      ring
    rw [qParameter, qParameter, hArg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · have hNorm : ‖jacobiTheta (w : ℂ)‖ < ‖jacobiTheta (z : ℂ)‖ :=
      translated_theta_norm_strictly_smaller (y := 2) (by norm_num)
    have hSq : ‖jacobiTheta (w : ℂ)‖ ^ 2 < ‖jacobiTheta (z : ℂ)‖ ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hNorm
    rw [quotientThetaDensity_apply, quotientThetaDensity_apply, thetaDensity, thetaDensity, hIm]
    exact mul_lt_mul_of_pos_left hSq (Real.sqrt_pos.2 z.im_pos)

theorem actual_theta_density_does_not_factor_through_printed_q :
    ¬ ∃ F : ℂ → ℝ, ∀ z : ℍ, F (qParameter z) = quotientThetaDensity (orbitPoint z) := by
  rintro ⟨F, hF⟩
  obtain ⟨z, w, hq, hθ⟩ := actual_theta_density_printed_q_collision
  rw [← hF w, ← hF z, hq] at hθ
  exact (lt_irrefl _) hθ

end
end ManuscriptAudit.Paper9ThetaQCoordinate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9ThetaQCoordinate.actual_theta_density_printed_q_collision,
      ``ManuscriptAudit.Paper9ThetaQCoordinate.actual_theta_density_does_not_factor_through_printed_q] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
