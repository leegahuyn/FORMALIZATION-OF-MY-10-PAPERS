import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecificLimits.Normed
import PrimalitySheafVerification.ManuscriptAudit.Paper4PrintedRootApproximation

/-! The printed linear approximation to the actual root shift is asymptotic
to the shift at every fixed real base greater than one. -/

namespace ManuscriptAudit.Paper4PrintedRootAsymptotic

open Filter Topology
open Paper4PrintedRealRootShift (printedRoot)
open Paper4PrintedRootApproximation (relative_error_bound)

noncomputable section

theorem scaled_shift_tendsto_one (A : ℝ) (hA : 1 < A) :
    Tendsto (fun p : ℕ ↦ A ^ (p - 1) * (printedRoot A p - A)) atTop (𝓝 1) := by
  have hPos : 0 < A := zero_lt_one.trans hA
  have hUpper : Tendsto (fun p : ℕ ↦ (p : ℝ) / A ^ p) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hA
  have hError : Tendsto (fun p : ℕ ↦ 1 - A ^ (p - 1) * (printedRoot A p - A))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with p hp
      exact (relative_error_bound A hPos p hp).1.le
    · filter_upwards [eventually_gt_atTop (1 : ℕ)] with p hp
      have hExp : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.sub_le p 1
      exact (relative_error_bound A hPos p hp).2.trans
        (div_le_div_of_nonneg_right hExp (pow_nonneg hPos.le _))
  have hOne : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_zero, sub_sub_cancel] using hOne.sub hError

end
end ManuscriptAudit.Paper4PrintedRootAsymptotic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper4PrintedRootAsymptotic.scaled_shift_tendsto_one
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
