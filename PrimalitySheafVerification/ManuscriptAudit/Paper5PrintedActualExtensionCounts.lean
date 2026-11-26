import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitExtensionRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedSupersingular

/-! Every higher trace in the Paper 5 table is the trace of actual extension-field points. -/

namespace ManuscriptAudit.Paper5PrintedActualExtensionCounts

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open Paper5PrintedRecurrence

noncomputable section

theorem actual_extension_trace_eq_recurrence {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    {A : ZMod p} (hA : A ≠ 0) :
    (Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ) =
      recurrence p ((p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ))
        (Module.finrank (ZMod p) E) := by
  have h3 := CubicTraceClassification.prime_rem_three_ne_zero (p := p) hp
  by_cases h1 : p % 3 = 1
  · exact Paper5ExtensionRecurrence.actual_extension_trace_eq_recurrence hp h1 hA
  · have h2 : p % 3 = 2 := by omega
    exact Paper5NonsplitExtensionRecurrence.actual_extension_trace_eq_recurrence_of_mod_two
      hp h2 hA

/-- A printed trace column gives the point-count trace on any actual
extension of the corresponding degree. -/
theorem printedRows_actual_extension_trace_at {r : Row} (hr : r ∈ printedRows) (i : Fin 6)
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod r.prime) E]
    (hd : Module.finrank (ZMod r.prime) E = i.val + 1) :
    (Fintype.card E : ℤ) + 1 -
      (Nat.card ((paper5TraceCurve r.prime (1 : ZMod r.prime)).baseChange E).toProjective.Point : ℤ)
       = (r.traceColumns[i.val]?).getD 0 := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  have hp := Paper5PrintedSupersingular.printedRows_prime_at_least_five hr
  rw [actual_extension_trace_eq_recurrence hp (one_ne_zero : (1 : ZMod r.prime) ≠ 0),
    Paper5PrintedPointCounts.printedRows_actual_firstTrace hr, hd, printedRows_recurrence hr]
  simp [Row.recurrenceColumns, i.isLt]

end
end ManuscriptAudit.Paper5PrintedActualExtensionCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5PrintedActualExtensionCounts.actual_extension_trace_eq_recurrence,
      ``ManuscriptAudit.Paper5PrintedActualExtensionCounts.printedRows_actual_extension_trace_at] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
