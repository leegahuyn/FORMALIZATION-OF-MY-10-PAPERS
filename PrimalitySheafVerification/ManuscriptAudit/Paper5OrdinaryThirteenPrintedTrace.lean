import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts

/-! The printed characteristic-thirteen row agrees with the actual Tate traces. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenPrintedTrace

open Paper5OrdinaryThirteenCoordinates Paper5OrdinaryThirteenTate
open Paper5LinearTraceRecurrence Paper5PrintedRecurrence Paper5PrintedPointCounts PowerTateModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 13) L] [CharP L 13] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

def thirteenRow : Row := ⟨6, 13, 12, 2, -22, -70, 146, 1202, 506⟩

theorem thirteenRow_mem : thirteenRow ∈ printedRows := by decide

theorem trace_power (hl : l = 2 ∨ l = 3) (n : ℕ) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l ^ n) =
      (recurrence 13 2 n : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det L l hl
  exact trace_pow_eq_recurrence (tateBasis L l hl) (action L l) 13 2
    (by simpa only [Int.cast_ofNat] using ht) hd n

theorem six_trace_columns (hl : l = 2 ∨ l = 3) :
    (List.range 6).map (fun i =>
      LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l ^ (i + 1))) =
        thirteenRow.traceColumns.map (fun a : ℤ => (a : ℤ_[l])) := by
  rw [printedRows_recurrence thirteenRow_mem, Row.recurrenceColumns, List.map_map]
  simp only [trace_power L l hl, thirteenRow]
  apply congrArg (fun f : ℕ → ℤ_[l] => (List.range 6).map f)
  funext i
  rfl

theorem trace_eq_signed_count (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l) =
      (((13 + 1 - (Nat.card (paper5TraceCurve 13 (1 : ZMod 13)).toProjective.Point : ℤ)) : ℤ) : ℤ_[l]) := by
  have h := printedRows_actual_firstTrace thirteenRow_mem
  change (13 : ℤ) + 1 - (Nat.card (paper5TraceCurve 13 (1 : ZMod 13)).toProjective.Point : ℤ) = 2 at h
  have h' := congrArg (fun a : ℤ => (a : ℤ_[l])) h
  exact (trace_det L l hl).1.trans (by simpa only [Int.cast_ofNat] using h'.symm)

end
end ManuscriptAudit.Paper5OrdinaryThirteenPrintedTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenPrintedTrace.trace_power,
      ``ManuscriptAudit.Paper5OrdinaryThirteenPrintedTrace.six_trace_columns,
      ``ManuscriptAudit.Paper5OrdinaryThirteenPrintedTrace.trace_eq_signed_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
