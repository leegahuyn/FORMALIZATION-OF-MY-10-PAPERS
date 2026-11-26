import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterTables
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts

/-!
# Actual point counts for the page 166 data at two constants

All later point counts agree with the actual cubic for A = 4. The
appendix's A = 1 gives the earlier table, so the paired comparison
locates exactly where it differs from the later printed count.
-/

namespace ManuscriptAudit.Paper5LaterPointCounts

open PrimalitySheafVerification.ManuscriptAudit
open Paper5LaterTables Paper5PrintedPointCounts

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
private theorem countRows_checks_A4 :
    ∀ r ∈ countRows, 5 ≤ r.prime ∧ r.prime.Prime ∧ countedPointsFor r.prime 4 = r.points := by
  decide

/-- The later printed count coincides with the actual curve with A = 4, row by row. -/
theorem actual_point_counts_A4 {r : CountRow} (hr : r ∈ countRows) :
    Nat.card (paper5TraceCurve r.prime ((4 : ℕ) : ZMod r.prime)).toProjective.Point = r.points := by
  obtain ⟨hp5, hp, hc⟩ := countRows_checks_A4 r hr
  letI : Fact r.prime.Prime := ⟨hp⟩
  have hA : ((4 : ℕ) : ZMod r.prime) ≠ 0 := by
    intro hz
    have hv := congrArg ZMod.val hz
    have h4 : 4 < r.prime := Nat.lt_of_succ_le hp5
    have : (4 : ℕ) = 0 := by
      simpa only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt h4] using hv
    exact (by decide : (4 : ℕ) ≠ 0) this
  exact (projective_count_eq_countedFor hp5 hA).trans hc

theorem actual_traces_A4 {r : CountRow} (hr : r ∈ countRows) :
    (r.prime : ℤ) + 1 -
      (Nat.card (paper5TraceCurve r.prime ((4 : ℕ) : ZMod r.prime)).toProjective.Point : ℤ) =
      r.trace := by
  rw [actual_point_counts_A4 hr, all_count_trace_relations r hr]
  ring

private noncomputable def curveCountA1 (p : ℕ) : ℕ :=
  Nat.card (paper5TraceCurve p (1 : ZMod p)).toProjective.Point

private theorem paired_earlier_mem :
    ∀ r ∈ pairedCounts, r.1 ∈ Paper5PrintedRecurrence.printedRows := by decide

/-- The earlier table gives the actual A = 1 count at each prime in the paired rows. -/
theorem paired_actual_A1_iff_tables_agree {r : Paper5PrintedRecurrence.Row × CountRow}
    (hr : r ∈ pairedCounts) :
    Nat.card (paper5TraceCurve r.2.prime (1 : ZMod r.2.prime)).toProjective.Point = r.2.points ↔
      r.1.points = r.2.points := by
  change curveCountA1 r.2.prime = r.2.points ↔ r.1.points = r.2.points
  have hCount : curveCountA1 r.2.prime = r.1.points :=
    (congrArg curveCountA1 (paired_primes_agree r hr).symm).trans
      (printedRows_actual_point_counts (paired_earlier_mem r hr))
  rw [hCount]

end ManuscriptAudit.Paper5LaterPointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.Paper5LaterPointCounts.actual_point_counts_A4,
        ``ManuscriptAudit.Paper5LaterPointCounts.actual_traces_A4,
        ``ManuscriptAudit.Paper5LaterPointCounts.paired_actual_A1_iff_tables_agree] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
