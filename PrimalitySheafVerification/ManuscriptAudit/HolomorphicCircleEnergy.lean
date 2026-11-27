import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Convex.Integral

/-! The squared modulus at a holomorphic disc center is at most the circular average of the squared modulus. -/

namespace ManuscriptAudit.HolomorphicCircleEnergy

open Metric Set MeasureTheory
open scoped Interval

private theorem convexOn_norm_sq :
    ConvexOn ℝ (univ : Set ℂ) (fun z : ℂ => ‖z‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hNorm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] using
      norm_add_le (a • x) (b • y)
  have hSq : 0 ≤ a * b * (‖x‖ - ‖y‖) ^ 2 := by positivity
  calc
    ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hNorm 2
    _ = (a + b) * (a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2) - a * b * (‖x‖ - ‖y‖) ^ 2 := by ring
    _ ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
      rw [hab, one_mul]
      exact sub_le_self _ hSq

theorem norm_sq_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (h : DiffContOnCl ℂ f (ball c |r|)) :
    ‖f c‖ ^ 2 ≤ Real.circleAverage (fun z : ℂ => ‖f z‖ ^ 2) c r := by
  let F (θ : ℝ) := f (circleMap c r θ)
  have hF : Continuous F := h.continuousOn_ball.comp_continuous (continuous_circleMap c r)
    (fun θ => sphere_subset_closedBall (circleMap_mem_sphere' c r θ))
  have hInt := intervalIntegrable_iff.mp (hF.intervalIntegrable 0 (2 * Real.pi))
  have hIntSq := intervalIntegrable_iff.mp ((hF.norm.pow 2).intervalIntegrable 0 (2 * Real.pi))
  have hVol : volume (Ι (0 : ℝ) (2 * Real.pi)) ≠ 0 := by
    rw [uIoc_of_le Real.two_pi_pos.le, Real.volume_Ioc, sub_zero]
    exact (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne'
  have hTop : volume (Ι (0 : ℝ) (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hConv := convexOn_norm_sq.map_set_average_le
    (continuous_norm.pow 2).continuousOn isClosed_univ hVol hTop
    (Filter.Eventually.of_forall (fun θ => mem_univ (F θ))) hInt hIntSq
  rw [← h.circleAverage]
  simpa only [Real.circleAverage_eq_intervalAverage, Function.comp_apply, F] using hConv

end ManuscriptAudit.HolomorphicCircleEnergy

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.HolomorphicCircleEnergy.norm_sq_le_circleAverage
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
