import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtyOneTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTatePointCounts

/-! The printed characteristic-thirty-one row agrees with the actual Tate traces. -/

namespace ManuscriptAudit.Paper5OrdinaryThirtyOnePrintedTrace

open Paper5OrdinaryThirtyOneCoordinates Paper5OrdinaryThirtyOneTate
open Paper5LinearTraceRecurrence Paper5PrintedRecurrence Paper5PrintedPointCounts PowerTateModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

local instance : Fact (Nat.Prime 31) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 31) L] [CharP L 31] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

def thirtyOneRow : Row := ⟨11, 31, 36, -4, -46, 308, 194, -10324, 35282⟩

theorem thirtyOneRow_mem : thirtyOneRow ∈ printedRows := by decide

theorem trace_power (hl : l = 2 ∨ l = 3) (n : ℕ) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l ^ n) =
      (recurrence 31 (-4) n : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det L l hl
  exact trace_pow_eq_recurrence (tateBasis L l hl) (action L l) 31 (-4)
    (by simpa only [Int.cast_neg, Int.cast_ofNat] using ht) hd n

theorem six_trace_columns (hl : l = 2 ∨ l = 3) :
    (List.range 6).map (fun i =>
      LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l ^ (i + 1))) =
        thirtyOneRow.traceColumns.map (fun a : ℤ => (a : ℤ_[l])) := by
  rw [printedRows_recurrence thirtyOneRow_mem, Row.recurrenceColumns, List.map_map]
  simp only [trace_power L l hl, thirtyOneRow]
  apply congrArg (fun f : ℕ → ℤ_[l] => (List.range 6).map f)
  funext i
  rfl

theorem trace_eq_signed_count (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l) =
      (((31 + 1 - (Nat.card (paper5TraceCurve 31 (1 : ZMod 31)).toProjective.Point : ℤ)) : ℤ) : ℤ_[l]) := by
  have h := printedRows_actual_firstTrace thirtyOneRow_mem
  change (31 : ℤ) + 1 - (Nat.card (paper5TraceCurve 31 (1 : ZMod 31)).toProjective.Point : ℤ) = -4 at h
  have h' := congrArg (fun a : ℤ => (a : ℤ_[l])) h
  exact (trace_det L l hl).1.trans (by simpa only [Int.cast_neg, Int.cast_ofNat] using h'.symm)

theorem trace_eq_extension_count
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod 31) E]
    (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l ^ Module.finrank (ZMod 31) E) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve 31 (1 : ZMod 31)).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  exact Paper5SplitTatePointCounts.trace_power_eq_extension_count (p := 31) (E := E)
    (by decide) (by decide) (one_ne_zero : (1 : ZMod 31) ≠ 0)
    (tateBasis L l hl) (action L l) (trace_eq_signed_count L l hl)
    (by simpa only [Nat.cast_ofNat] using (trace_det L l hl).2)

end
end ManuscriptAudit.Paper5OrdinaryThirtyOnePrintedTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirtyOnePrintedTrace.trace_power,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOnePrintedTrace.six_trace_columns,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOnePrintedTrace.trace_eq_signed_count,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOnePrintedTrace.trace_eq_extension_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
