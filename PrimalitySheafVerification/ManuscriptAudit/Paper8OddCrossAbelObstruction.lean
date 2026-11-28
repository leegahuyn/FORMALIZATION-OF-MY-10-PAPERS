import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.MetricSpace.Bounded
import PrimalitySheafVerification.ManuscriptAudit.Paper8BoundaryLaplace
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspCutoff

/-! The manuscript's ordered signed cross cutoff cannot coexist with a nonzero off-real Abel residue. -/

namespace ManuscriptAudit.Paper8OddCrossAbelObstruction

open Set Filter MeasureTheory Paper8BoundaryLaplace Paper8OddCrossCuspCutoff
open scoped Topology Nat

noncomputable section

def orderedCrossCutoff (N : ℕ) : ℂ := ∑ j ∈ Finset.range N, crossRaw j

def crossLogarithmicStep (t : ℝ) : ℂ := orderedCrossCutoff ⌊Real.exp t⌋₊

def crossAbelShiftedZeta (w : ℂ) : ℂ :=
  (2 : ℂ) ^ (-(w + 1)) * w * boundaryLaplace crossLogarithmicStep w

private theorem tendsto_floor_exp : Tendsto (fun t : ℝ => ⌊Real.exp t⌋₊) atTop atTop := by
  refine tendsto_atTop.2 fun N => ?_
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (N : ℝ)] with t ht
  exact Nat.le_floor ht

theorem crossLogarithmicStep_measurable : Measurable crossLogarithmicStep := by
  unfold crossLogarithmicStep
  exact (measurable_of_countable orderedCrossCutoff).comp (Real.continuous_exp.measurable.nat_floor)

theorem ordered_cross_cutoff_forces_zero_abel_residue {L : ℂ}
    (hL : Tendsto orderedCrossCutoff atTop (𝓝 L)) {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * crossAbelShiftedZeta ((ε : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1
    (Metric.isBounded_range_of_tendsto orderedCrossCutoff hL)
  have hb (t : ℝ) (_ : 0 < t) : ‖crossLogarithmicStep t‖ ≤ C := by
    have h := hC (show crossLogarithmicStep t ∈ Set.range orderedCrossCutoff from ⟨_, rfl⟩)
    have ht := Metric.mem_ball.1 h
    simpa only [dist_zero_right] using ht.le
  let w (ε : ℝ) : ℂ := (ε : ℂ) + (τ : ℂ) * Complex.I
  have hT : Tendsto (fun ε : ℝ => (ε : ℂ) * boundaryLaplace crossLogarithmicStep (w ε))
      (𝓝[>] 0) (𝓝 0) :=
    off_real_scaled_boundaryLaplace_tendsto_zero crossLogarithmicStep crossLogarithmicStep_measurable
      hb (hL.comp tendsto_floor_exp) hτ
  have hw : Continuous w := Complex.continuous_ofReal.add continuous_const
  have hF : Continuous (fun ε : ℝ => (2 : ℂ) ^ (-(w ε + 1)) * w ε) := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    simp_rw [Complex.cpow_def_of_ne_zero h2]
    exact (Complex.continuous_exp.comp (continuous_const.mul (hw.add continuous_const).neg)).mul hw
  have hNorm : Tendsto (fun ε : ℝ => (2 : ℂ) ^ (-(w ε + 1)) * w ε) (𝓝[>] 0)
      (𝓝 ((2 : ℂ) ^ (-(w 0 + 1)) * w 0)) := hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [crossAbelShiftedZeta, w, mul_zero, mul_assoc, mul_left_comm, mul_comm] using hNorm.mul hT

theorem no_ordered_cross_cutoff_limit_of_nonzero_abel_residue {τ : ℝ} (hτ : τ ≠ 0)
    {r : ℂ} (hr : r ≠ 0)
    (hPole : Tendsto (fun ε : ℝ => (ε : ℂ) * crossAbelShiftedZeta ((ε : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 r)) :
    ¬ ∃ L : ℂ, Tendsto orderedCrossCutoff atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  exact hr (tendsto_nhds_unique hPole (ordered_cross_cutoff_forces_zero_abel_residue hL hτ))

theorem no_ordered_cross_cutoff_limit_of_nonzero_zeta_pole {P : ℂ → ℂ} {τ : ℝ} (hτ : τ ≠ 0)
    {r : ℂ} (hr : r ≠ 0)
    (hAgree : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      P (((1 : ℂ) + (ε : ℂ) + (τ : ℂ) * Complex.I) / 2) =
        crossAbelShiftedZeta ((ε : ℂ) + (τ : ℂ) * Complex.I))
    (hPole : Tendsto (fun ε : ℝ => (ε : ℂ) * P (((1 : ℂ) + (ε : ℂ) + (τ : ℂ) * Complex.I) / 2))
      (𝓝[>] 0) (𝓝 r)) :
    ¬ ∃ L : ℂ, Tendsto orderedCrossCutoff atTop (𝓝 L) :=
  no_ordered_cross_cutoff_limit_of_nonzero_abel_residue hτ hr
    (hPole.congr' (hAgree.mono fun ε h => congrArg (fun x : ℂ => (ε : ℂ) * x) h))

end
end ManuscriptAudit.Paper8OddCrossAbelObstruction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossAbelObstruction.no_ordered_cross_cutoff_limit_of_nonzero_zeta_pole
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
