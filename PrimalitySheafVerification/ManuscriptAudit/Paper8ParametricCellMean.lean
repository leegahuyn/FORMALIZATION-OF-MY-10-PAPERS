import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PrimalitySheafVerification.ManuscriptAudit.Paper8IntervalCellApproximation

/-! Continuity and vertical differentiation of a horizontal interval cell average. -/

namespace ManuscriptAudit.Paper8ParametricCellMean

open MeasureTheory Filter Set Paper8IntervalCellApproximation
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem cell_slice_continuous {F : ℝ → ℝ → E}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (y : ℝ) :
    Continuous (fun x => F x y) :=
  hF.comp (continuous_id.prodMk continuous_const)

private theorem cell_derivative_slice_continuous {F : ℝ → ℝ → E}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (x : ℝ) :
    Continuous (fun y => F x y) :=
  hF.comp (continuous_const.prodMk continuous_id)

private theorem exists_cell_local_bound {F : ℝ → ℝ → E}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (a b y : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ∀ t ∈ Metric.ball y 1, ‖F x t‖ ≤ C := by
  let R : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (y - 1) (y + 1)
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hR.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, fun x hx t ht => hC (x, t) ⟨hx, ?_⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem continuous_intervalIntegral_param {F : ℝ → ℝ → E}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun y => ∫ x in a..b, F x y) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨C, hC⟩ := exists_cell_local_bound hF a b y
  apply intervalIntegral.continuousAt_of_dominated_interval (μ := (volume : Measure ℝ))
    (bound := fun _ => C)
  · exact Eventually.of_forall (fun t => (cell_slice_continuous hF t).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0 : ℝ) < 1)] with t ht
    exact Eventually.of_forall (fun x hx => hC x
      (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hx)) t ht)
  · exact continuous_const.intervalIntegrable _ _
  · exact Eventually.of_forall (fun x _ => (cell_derivative_slice_continuous hF x).continuousAt)

theorem continuous_intervalCellMean_param {F : ℝ → ℝ → ℂ}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun y => intervalCellMean (fun x => F x y) a b) := by
  unfold intervalCellMean
  exact continuous_const.mul (continuous_intervalIntegral_param hF hab)

theorem hasDerivAt_intervalCellMean_param {F D : ℝ → ℝ → ℂ}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hD : Continuous (fun p : ℝ × ℝ => D p.1 p.2))
    (hDeriv : ∀ x y, HasDerivAt (fun t => F x t) (D x y) y)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    HasDerivAt (fun t => intervalCellMean (fun x => F x t) a b)
      (intervalCellMean (fun x => D x y) a b) y := by
  let μ := (volume : Measure ℝ).restrict (Ioc a b)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  obtain ⟨C, hC⟩ := exists_cell_local_bound hD a b y
  have hFm : ∀ᶠ t in 𝓝 y, AEStronglyMeasurable (fun x => F x t) μ :=
    Eventually.of_forall (fun t => (cell_slice_continuous hF t).measurable.aestronglyMeasurable)
  have hFi : Integrable (fun x => F x y) μ :=
    ((cell_slice_continuous hF y).intervalIntegrable a b).1
  have hDm : AEStronglyMeasurable (fun x => D x y) μ :=
    (cell_slice_continuous hD y).measurable.aestronglyMeasurable
  have hB : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball y 1, ‖D x t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (Ioc_subset_Icc_self hx)
  have hDi : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball y 1, HasDerivAt (fun s => F x s) (D x t) t :=
    Eventually.of_forall (fun x t _ => hDeriv x t)
  have hP := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds y (by norm_num : (0 : ℝ) < 1)) hFm hFi hDm hB (integrable_const C) hDi).2
  unfold intervalCellMean
  simp_rw [intervalIntegral.integral_of_le hab]
  exact hP.const_mul (((b - a)⁻¹ : ℝ) : ℂ)

end
end ManuscriptAudit.Paper8ParametricCellMean

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8ParametricCellMean.hasDerivAt_intervalCellMean_param
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
