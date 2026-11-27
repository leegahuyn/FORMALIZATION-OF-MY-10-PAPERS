import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryFortyThreeTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTatePointCounts

/-! The printed characteristic-43 row agrees with the actual Tate traces. -/

namespace ManuscriptAudit.Paper5OrdinaryFortyThreePrintedTrace

open Paper5OrdinaryFortyThreeFrobenius Paper5OrdinaryFortyThreeTate
open Paper5LinearTraceRecurrence Paper5PrintedRecurrence Paper5PrintedPointCounts PowerTateModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 43) L] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

def fortyThreeRow : Row := ⟨14, 43, 36, 8, -22, -520, -3214, -3352, 111386⟩

theorem fortyThreeRow_mem : fortyThreeRow ∈ printedRows := by decide

theorem trace_power (hl : l = 2 ∨ l = 3) (n : ℕ) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l ^ n) =
      (recurrence 43 8 n : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det L l hl
  exact trace_pow_eq_recurrence (tateBasis L l hl) (action L l) 43 8
    (by simpa only [Int.cast_neg, Int.cast_ofNat] using ht) hd n

theorem six_trace_columns (hl : l = 2 ∨ l = 3) :
    (List.range 6).map (fun i =>
      LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l ^ (i + 1))) =
        fortyThreeRow.traceColumns.map (fun a : ℤ => (a : ℤ_[l])) := by
  rw [printedRows_recurrence fortyThreeRow_mem, Row.recurrenceColumns, List.map_map]
  simp only [trace_power L l hl, fortyThreeRow]
  apply congrArg (fun f : ℕ → ℤ_[l] => (List.range 6).map f)
  funext i
  rfl

theorem trace_eq_signed_count (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l) =
      (((43 + 1 - (Nat.card (paper5TraceCurve 43 (1 : ZMod 43)).toProjective.Point : ℤ)) : ℤ) : ℤ_[l]) := by
  have h := printedRows_actual_firstTrace fortyThreeRow_mem
  change (43 : ℤ) + 1 - (Nat.card (paper5TraceCurve 43 (1 : ZMod 43)).toProjective.Point : ℤ) = 8 at h
  have h' := congrArg (fun a : ℤ => (a : ℤ_[l])) h
  exact (trace_det L l hl).1.trans (by simpa only [Int.cast_neg, Int.cast_ofNat] using h'.symm)

theorem trace_eq_extension_count
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod 43) E]
    (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l ^ Module.finrank (ZMod 43) E) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve 43 (1 : ZMod 43)).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  exact Paper5SplitTatePointCounts.trace_power_eq_extension_count (p := 43) (E := E)
    (by decide) (by decide) (one_ne_zero : (1 : ZMod 43) ≠ 0)
    (tateBasis L l hl) (action L l) (trace_eq_signed_count L l hl)
    (by simpa only [Nat.cast_ofNat] using (trace_det L l hl).2)

end
end ManuscriptAudit.Paper5OrdinaryFortyThreePrintedTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryFortyThreePrintedTrace.trace_power,
      ``ManuscriptAudit.Paper5OrdinaryFortyThreePrintedTrace.six_trace_columns,
      ``ManuscriptAudit.Paper5OrdinaryFortyThreePrintedTrace.trace_eq_signed_count,
      ``ManuscriptAudit.Paper5OrdinaryFortyThreePrintedTrace.trace_eq_extension_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
