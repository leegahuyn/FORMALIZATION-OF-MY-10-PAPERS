import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenOneTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence

/-! All six printed p=7 traces are traces of powers of the actual Tate action. -/

namespace ManuscriptAudit.Paper5OrdinarySevenPrintedTrace

open Paper5OrdinarySevenOneTate Paper5PrintedRecurrence
open Paper5LinearTraceRecurrence PowerTateModule

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

/-- The native Tate-action power trace for the printed ordinary fiber, in any degree. -/
theorem trace_power (hl : l = 2 ∨ l = 3) (n : ℕ) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric L)) (action L l ^ n) =
      (recurrence 7 (-4) n : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det L l hl
  exact trace_pow_eq_recurrence (tateBasis L l hl) (action L l) 7 (-4)
    (by simpa only [Int.cast_neg, Int.cast_ofNat] using ht) hd n

def sevenRow : Row := ⟨4, 7, 12, -4, 2, 20, -94, 236, -286⟩

theorem sevenRow_mem : sevenRow ∈ printedRows := by decide

/-- The six page-158 entries at p=7 agree with the actual 2-adic and 3-adic power traces. -/
theorem six_trace_columns (hl : l = 2 ∨ l = 3) :
    (List.range 6).map (fun i =>
      LinearMap.trace ℤ_[l] (Tate l (Geometric L)) (action L l ^ (i + 1))) =
        sevenRow.traceColumns.map (fun a : ℤ => (a : ℤ_[l])) := by
  rw [printedRows_recurrence sevenRow_mem, Row.recurrenceColumns, List.map_map]
  simpa only [trace_power L l hl, Function.comp_apply]

end
end ManuscriptAudit.Paper5OrdinarySevenPrintedTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenPrintedTrace.trace_power,
      ``ManuscriptAudit.Paper5OrdinarySevenPrintedTrace.sevenRow_mem,
      ``ManuscriptAudit.Paper5OrdinarySevenPrintedTrace.six_trace_columns] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
