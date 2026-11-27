import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Bounded
import PrimalitySheafVerification.ManuscriptAudit.Paper8CutoffLog
import PrimalitySheafVerification.ManuscriptAudit.Paper8AllResidueModeConvergence

/-!
# Logarithmic asymptotics of the actual signed even sector

The four arithmetic progression limits are explicit hypotheses.
The result computes the signed even main term and rules out a
finite ordinary limit if that main term is nonzero.
-/

namespace ManuscriptAudit.Paper8EvenCutoffLogLimit

open Filter
open scoped Topology
open Paper8CutoffLog (cutoffLog cutoffLog_pos cutoffLog_tendsto_atTop cutoffLog_ratio_bounds
  cutoffLog_ratio_tendsto_one)
open Paper8ContourResidueWeights (reducedResidues)
open Paper8ReciprocalCommonFourier (orderedFourierCoefficient)
open Paper8EvenGcdOrderedLimit (evenSectorCutoff evenWeight evenWeight_norm_summable
  evenSectorCutoff_eq_progressions progressionPartialSum unshiftedCoefficient)
open Paper8AllResidueModeConvergence (all_residue_mode_limit_iff_even)

noncomputable section

private theorem divided_index_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => N / d) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (b * d)] with N hN
  exact (Nat.le_div_iff_mul_le hd).2 hN

theorem weighted_divided_log_limits (f w : ℕ → ℂ) {L : ℂ}
    (hf : Tendsto (fun N => (cutoffLog N)⁻¹ • f N) atTop (𝓝 L))
    (hw : Summable (fun h : ℕ => ‖w h‖)) :
    Tendsto (fun N => ∑' h : ℕ, w h * ((cutoffLog N)⁻¹ • f (N / (h + 1)))) atTop
      (𝓝 (∑' h : ℕ, w h * L)) := by
  let G (N : ℕ) := (cutoffLog N)⁻¹ • f N
  let ρ (N h : ℕ) := cutoffLog (N / (h + 1)) / cutoffLog N
  let b (N h : ℕ) := w h * (ρ N h • G (N / (h + 1)))
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto G hf).exists_norm_le
  have hTerm (h : ℕ) : Tendsto (fun N => b N h) atTop (𝓝 (w h * L)) := by
    have hG : Tendsto (fun N => G (N / (h + 1))) atTop (𝓝 L) :=
      hf.comp (divided_index_tendsto (Nat.succ_pos h))
    have hρ : Tendsto (fun N => ρ N h) atTop (𝓝 1) :=
      cutoffLog_ratio_tendsto_one (Nat.succ_pos h)
    have hW : Tendsto (fun _ : ℕ => w h) atTop (𝓝 (w h)) := tendsto_const_nhds
    simpa only [one_smul] using hW.mul (hρ.smul hG)
  have hDom : ∀ᶠ N in atTop, ∀ h : ℕ, ‖b N h‖ ≤ ‖w h‖ * C := by
    exact Filter.Eventually.of_forall fun N h => by
      have hρ : 0 ≤ ρ N h ∧ ρ N h ≤ 1 := cutoffLog_ratio_bounds N (Nat.succ_pos h)
      have hg : ‖G (N / (h + 1))‖ ≤ C := hC _ ⟨N / (h + 1), rfl⟩
      change ‖w h * (ρ N h • G (N / (h + 1)))‖ ≤ ‖w h‖ * C
      rw [norm_mul, norm_smul, Real.norm_of_nonneg hρ.1]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ 1 * ‖G (N / (h + 1))‖ := mul_le_mul_of_nonneg_right hρ.2 (norm_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using hg
  have h := tendsto_tsum_of_dominated_convergence (hw.mul_right C) hTerm hDom
  refine h.congr fun N => tsum_congr fun j => ?_
  change w j * (ρ N j • ((cutoffLog (N / (j + 1)))⁻¹ • f (N / (j + 1)))) =
    w j * ((cutoffLog N)⁻¹ • f (N / (j + 1)))
  rw [smul_smul]
  have hScale : ρ N j * (cutoffLog (N / (j + 1)))⁻¹ = (cutoffLog N)⁻¹ := by
    unfold ρ
    field_simp [(cutoffLog_pos N).ne', (cutoffLog_pos (N / (j + 1))).ne'] <;> ring
  rw [hScale]

theorem even_sector_log_limit (n : ℕ) (A : ℕ → ℂ)
    (hA : ∀ r ∈ Finset.range 4, Tendsto (fun N => (cutoffLog N)⁻¹ •
      progressionPartialSum (fun D => unshiftedCoefficient D n) r N) atTop (𝓝 (A r))) :
    Tendsto (fun N => (cutoffLog N)⁻¹ • evenSectorCutoff N n) atTop
      (𝓝 (∑ r ∈ Finset.range 4, (∑' h : ℕ, evenWeight (h + 1) r) * A r)) := by
  have h := tendsto_finsetSum (Finset.range 4) (fun r hr =>
    weighted_divided_log_limits (progressionPartialSum (fun D => unshiftedCoefficient D n) r)
      (fun h => evenWeight (h + 1) r) (hA r hr) (evenWeight_norm_summable r))
  simp only [tsum_mul_right] at h
  refine h.congr fun N => ?_
  rw [evenSectorCutoff_eq_progressions, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  change (∑' h : ℕ, evenWeight (h + 1) r *
      ((cutoffLog N)⁻¹ • progressionPartialSum (fun D => unshiftedCoefficient D n) r (N / (h + 1)))) =
      (((cutoffLog N)⁻¹ : ℝ) : ℂ) *
        (∑' h : ℕ, evenWeight (h + 1) r *
          progressionPartialSum (fun D => unshiftedCoefficient D n) r (N / (h + 1)))
  rw [← tsum_mul_left]
  refine tsum_congr fun h => ?_
  rw [Complex.real_smul]
  ring

theorem even_sector_no_ordered_limit_of_log_limit (n : ℕ) {L : ℂ} (hL : L ≠ 0)
    (hLog : Tendsto (fun N => (cutoffLog N)⁻¹ • evenSectorCutoff N n) atTop (𝓝 L)) :
    ¬ ∃ B : ℂ, Tendsto (fun N => evenSectorCutoff N n) atTop (𝓝 B) := by
  rintro ⟨B, hB⟩
  have hi : Tendsto (fun N => (cutoffLog N)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp cutoffLog_tendsto_atTop
  have hz : Tendsto (fun N => (cutoffLog N)⁻¹ • evenSectorCutoff N n) atTop (𝓝 0) := by
    simpa only [zero_smul] using hi.smul hB
  exact hL (tendsto_nhds_unique hLog hz)

theorem all_residue_mode_no_ordered_limit_of_even_log_limit (n : ℕ) {L C : ℂ} (hL : L ≠ 0)
    (hLog : Tendsto (fun N => (cutoffLog N)⁻¹ • evenSectorCutoff N n) atTop (𝓝 L))
    (hC : Tendsto (fun N => orderedFourierCoefficient reducedResidues N n) atTop (𝓝 C)) :
    ¬ ∃ B : ℂ, Tendsto (fun N => orderedFourierCoefficient (fun _ => Finset.univ) N n)
      atTop (𝓝 B) := by
  rintro ⟨B, hB⟩
  exact even_sector_no_ordered_limit_of_log_limit n hL hLog
    ⟨_, (all_residue_mode_limit_iff_even n hC B).1 hB⟩

end
end ManuscriptAudit.Paper8EvenCutoffLogLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenCutoffLogLimit.weighted_divided_log_limits,
      ``ManuscriptAudit.Paper8EvenCutoffLogLimit.even_sector_log_limit,
      ``ManuscriptAudit.Paper8EvenCutoffLogLimit.even_sector_no_ordered_limit_of_log_limit,
      ``ManuscriptAudit.Paper8EvenCutoffLogLimit.all_residue_mode_no_ordered_limit_of_even_log_limit] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
