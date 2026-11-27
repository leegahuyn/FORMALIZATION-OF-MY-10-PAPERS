import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HolomorphicStripEnergy

/-! Weighted square integrability and periodic magnitude force at most linear height growth. -/

namespace ManuscriptAudit.HolomorphicStripPointwise

open Set Filter Metric MeasureTheory
open HolomorphicStripEnergy
open scoped Topology Interval

theorem eventually_norm_le_mul_height (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) {w : ℝ} (hw : 0 < w)
    (hPer : ∀ y : ℝ, 0 < y →
      Function.Periodic (fun x : ℝ => ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) w)
    (hLTwo : IntegrableOn (weightedEnergy H w) (Ioi 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z : ℂ in comap Complex.im atTop, ‖H z‖ ≤ M * z.im := by
  let r : ℝ := min 1 (w / 2)
  let E : ℝ := ∫ y in Ioi (1 : ℝ), weightedEnergy H w y
  let A : ℝ := Real.pi * r ^ 2
  let C : ℝ := 4 * E / A
  have hr : 0 < r := lt_min zero_lt_one (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrW : 2 * r ≤ w := by
    have h := min_le_right 1 (w / 2)
    linarith
  have hE : 0 ≤ E := by
    refine setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
    unfold weightedEnergy horizontalEnergy
    exact div_nonneg (intervalIntegral.integral_nonneg_of_forall hw.le (fun x => sq_nonneg _))
      (Real.rpow_nonneg (by linarith [show 1 < y from hy]) _)
  have hA : 0 < A := by unfold A; positivity
  have hC : 0 ≤ C := by unfold C; positivity
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [preimage_mem_comap (Ici_mem_atTop (2 : ℝ))] with z hz
  have hz2 : (2 : ℝ) ≤ z.im := hz
  have hz0 : 0 < z.im := by linarith
  have hY : 1 ≤ z.im - r := by linarith
  have hClosed : DifferentiableOn ℂ H (closedBall z r) := by
    refine hH.mono (fun q hq => ?_)
    have hIm : |(q - z).im| ≤ r :=
      (Complex.abs_im_le_norm (q - z)).trans (mem_closedBall_iff_norm.mp hq)
    have hLow := (abs_le.mp hIm).1
    rw [Complex.sub_im] at hLow
    change 0 < q.im
    linarith
  have hBound : A * ‖H z‖ ^ 2 ≤ (z.im + r) ^ 2 * E :=
    (HolomorphicDiskEnergy.norm_sq_le_disk_energy hr hClosed).trans
      (disk_energy_le_weighted_cusp_energy H hH hw hPer hLTwo z hr hrW hY)
  have hLarger : (z.im + r) ^ 2 * E ≤ 4 * E * z.im ^ 2 := by
    calc
      _ ≤ (2 * z.im) ^ 2 * E := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity : 0 ≤ z.im + r) (by linarith) 2) hE
      _ = _ := by ring
  have hSquared : ‖H z‖ ^ 2 ≤ (Real.sqrt C * z.im) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    unfold C
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hA).2 (by simpa only [mul_comm (‖H z‖ ^ 2) A] using hBound.trans hLarger)
  have hRhs : 0 ≤ Real.sqrt C * z.im := mul_nonneg (Real.sqrt_nonneg _) hz0.le
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hRhs] using Real.sqrt_le_sqrt hSquared

end ManuscriptAudit.HolomorphicStripPointwise

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.HolomorphicStripPointwise.eventually_norm_le_mul_height
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
