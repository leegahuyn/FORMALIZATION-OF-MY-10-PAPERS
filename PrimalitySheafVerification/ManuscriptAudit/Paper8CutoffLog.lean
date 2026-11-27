import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The natural divided cutoffs have the same logarithmic normalizing scale. -/

namespace ManuscriptAudit.Paper8CutoffLog

open Filter
open scoped Topology

noncomputable section

def cutoffLog (N : ℕ) : ℝ := Real.log ((N + 2 : ℕ) : ℝ)

theorem cutoffLog_pos (N : ℕ) : 0 < cutoffLog N := by
  apply Real.log_pos
  exact_mod_cast (show 1 < N + 2 by omega)

theorem cutoffLog_tendsto_atTop : Tendsto cutoffLog atTop atTop := by
  have hN : Tendsto (fun N : ℕ => N + 2) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop b).mono fun N hN => ?_
    change b ≤ N + 2
    omega
  exact Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hN)

theorem cutoffLog_difference_bounds (N : ℕ) {d : ℕ} (hd : 0 < d) :
    0 ≤ cutoffLog N - cutoffLog (N / d) ∧
      cutoffLog N - cutoffLog (N / d) ≤ Real.log (d : ℝ) := by
  have hN : N + 2 ≤ d * (N / d + 2) := by
    have hm := Nat.mod_lt N hd
    have hSum := Nat.mod_add_div N d
    rw [Nat.mul_add, show d * 2 = 2 * d by omega]
    omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hBig : cutoffLog N ≤ Real.log (d : ℝ) + cutoffLog (N / d) := by
    unfold cutoffLog
    rw [← Real.log_mul hdR.ne' (by positivity)]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hN
  have hSmall : cutoffLog (N / d) ≤ cutoffLog N := by
    unfold cutoffLog
    apply Real.log_le_log (by positivity)
    exact_mod_cast (Nat.add_le_add_right (Nat.div_le_self N d) 2)
  exact ⟨sub_nonneg.mpr hSmall, by linarith⟩

theorem cutoffLog_ratio_bounds (N : ℕ) {d : ℕ} (hd : 0 < d) :
    0 ≤ cutoffLog (N / d) / cutoffLog N ∧ cutoffLog (N / d) / cutoffLog N ≤ 1 := by
  refine ⟨div_nonneg (cutoffLog_pos _).le (cutoffLog_pos _).le, ?_⟩
  apply (div_le_one₀ (cutoffLog_pos N)).2
  exact sub_nonneg.mp (cutoffLog_difference_bounds N hd).1

theorem cutoffLog_ratio_tendsto_one {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N => cutoffLog (N / d) / cutoffLog N) atTop (𝓝 1) := by
  have hi : Tendsto (fun N => (cutoffLog N)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp cutoffLog_tendsto_atTop
  have hc : Tendsto (fun _ : ℕ => Real.log (d : ℝ)) atTop (𝓝 (Real.log (d : ℝ))) :=
    tendsto_const_nhds
  have hBound : Tendsto (fun N => Real.log (d : ℝ) / cutoffLog N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hc.mul hi
  have hSmall : Tendsto (fun N =>
      (cutoffLog N - cutoffLog (N / d)) / cutoffLog N) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hBound ?_ ?_
    · intro N
      exact div_nonneg (cutoffLog_difference_bounds N hd).1 (cutoffLog_pos N).le
    · intro N
      exact div_le_div_of_nonneg_right (cutoffLog_difference_bounds N hd).2 (cutoffLog_pos N).le
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h : Tendsto (fun N => 1 -
      (cutoffLog N - cutoffLog (N / d)) / cutoffLog N) atTop (𝓝 1) := by
    simpa only [sub_zero] using hOne.sub hSmall
  apply h.congr
  intro N
  field_simp [(cutoffLog_pos N).ne'] <;> ring

end
end ManuscriptAudit.Paper8CutoffLog

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8CutoffLog.cutoffLog_difference_bounds,
      ``ManuscriptAudit.Paper8CutoffLog.cutoffLog_ratio_bounds,
      ``ManuscriptAudit.Paper8CutoffLog.cutoffLog_ratio_tendsto_one] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
