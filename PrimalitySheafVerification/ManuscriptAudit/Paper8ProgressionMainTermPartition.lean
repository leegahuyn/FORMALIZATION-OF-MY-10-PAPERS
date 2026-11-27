import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProgressionSqrtMainTerm

/-!
# Compatibility of the four progression constants with the aggregate

The aggregate square-root asymptotic fixes the sum of the four
progression constants. The signed even logarithmic main term uses
their separate weighted combination.
-/

namespace ManuscriptAudit.Paper8ProgressionMainTermPartition

open Filter
open scoped Topology
open Paper8UnshiftedZeroMode (squareRootScale rawTerm)
open Paper8ProgressionSqrtMainTerm (zeroModeProgressionRaw)

noncomputable section

theorem raw_progression_partition (N : ℕ) :
    (∑ r ∈ Finset.range 4, ∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw r j) =
      ∑ j ∈ Finset.range (N + 1), rawTerm j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold zeroModeProgressionRaw
  rw [Finset.sum_eq_single_of_mem ((j + 1) % 4)
    (Finset.mem_range.mpr (Nat.mod_lt _ (by decide))) (fun r _ h => if_neg (Ne.symm h)),
    if_pos rfl]

theorem progression_main_constants_sum_eq {A : ℕ → ℂ} {B : ℂ}
    (hA : ∀ r ∈ Finset.range 4, Tendsto (fun N => (squareRootScale N)⁻¹ •
      ∑ j ∈ Finset.range (N + 1), zeroModeProgressionRaw r j) atTop (𝓝 (A r)))
    (hB : Tendsto (fun N => (squareRootScale N)⁻¹ •
      ∑ j ∈ Finset.range (N + 1), rawTerm j) atTop (𝓝 B)) :
    (∑ r ∈ Finset.range 4, A r) = B := by
  have h := tendsto_finsetSum (Finset.range 4) hA
  have h' : Tendsto (fun N => (squareRootScale N)⁻¹ •
      ∑ j ∈ Finset.range (N + 1), rawTerm j) atTop (𝓝 (∑ r ∈ Finset.range 4, A r)) := by
    refine h.congr fun N => ?_
    rw [← Finset.smul_sum, raw_progression_partition]
  exact tendsto_nhds_unique h' hB

end
end ManuscriptAudit.Paper8ProgressionMainTermPartition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ProgressionMainTermPartition.raw_progression_partition,
      ``ManuscriptAudit.Paper8ProgressionMainTermPartition.progression_main_constants_sum_eq] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
