import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaSquaredModularity
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaCuspUnit

/-! The actual eta norm law and uniform lower bound in a positive-width cusp coordinate. -/

namespace ManuscriptAudit.Paper8ActualEtaNormCusp

open Set UpperHalfPlane Filter Function.Periodic
open Paper8ActualEtaSquaredModularity Paper8ActualEtaCuspUnit
open scoped MatrixGroups Topology

theorem eta_norm_square_transform (g : SL(2, ℤ)) (z : ℍ) :
    ‖ModularForm.eta (g • z : ℍ)‖ ^ 2 =
      ‖denominator g z‖ * ‖ModularForm.eta z‖ ^ 2 := by
  apply (pow_left_inj₀ (by positivity) (by positivity) (by decide : (12 : ℕ) ≠ 0)).mp
  have h := congrArg (fun v : ℂ => ‖v‖) (eta_pow_twentyFour_transform g z)
  simpa only [norm_mul, norm_pow, mul_pow, ← pow_mul] using h

private theorem product_norm_tendsto_one :
    Tendsto (fun z : ℍ => ‖widthUnit 1 (qParam 1 z)‖) atImInfty (𝓝 1) := by
  have hAt : ContinuousAt (widthUnit 1) 0 :=
    ((widthUnit_differentiableOn (w := 1) (by decide)).differentiableAt
      (Metric.ball_mem_nhds _ (by norm_num))).continuousAt
  have hP := hAt.tendsto.comp (qParam_tendsto_atImInfty (h := 1) (by norm_num))
  simpa only [widthUnit_at_zero (w := 1) (by decide), norm_one] using hP.norm

theorem eta_q_norm_eq_width_power {w : ℕ} (hw : 0 < w) (z : ℍ) :
    ‖qParam 24 z‖ = ‖qParam (w : ℝ) z‖ ^ ((w : ℝ) / 24) := by
  have hwR : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  rw [norm_qParam, norm_qParam, ← Real.exp_mul]
  congr 1
  field_simp [hwR] <;> ring

theorem eta_eventual_lower_bound {w : ℕ} (hw : 0 < w) :
    ∀ᶠ z : ℍ in atImInfty,
      (1 / 2 : ℝ) * ‖qParam (w : ℝ) z‖ ^ ((w : ℝ) / 24) ≤ ‖ModularForm.eta z‖ := by
  filter_upwards [product_norm_tendsto_one.eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with z hz
  have hProd : (∏' n : ℕ, (1 - ModularForm.eta_q n z)) = widthUnit 1 (qParam 1 z) := by
    simp [widthUnit, ModularForm.eta_q]
  rw [← eta_q_norm_eq_width_power hw, ModularForm.eta, norm_mul, hProd]
  simpa only [mul_comm (1 / 2 : ℝ)] using
    mul_le_mul_of_nonneg_left hz.le (norm_nonneg (qParam 24 z))

end ManuscriptAudit.Paper8ActualEtaNormCusp

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaNormCusp.eta_norm_square_transform,
      ``ManuscriptAudit.Paper8ActualEtaNormCusp.eta_q_norm_eq_width_power,
      ``ManuscriptAudit.Paper8ActualEtaNormCusp.eta_eventual_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
