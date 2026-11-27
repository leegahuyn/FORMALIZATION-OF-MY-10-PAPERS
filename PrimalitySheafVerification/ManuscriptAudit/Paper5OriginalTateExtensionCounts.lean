import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedAllTateDeterminants
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedActualExtensionCounts

/-! The actual extension counts agree with the native Tate power coefficients in every original row. -/

namespace ManuscriptAudit.Paper5OriginalTateExtensionCounts

open Paper5PrintedRecurrence Paper5PrintedNonsplitTateTraces Paper5PrintedAllTateDeterminants
open Paper5PrintedActualExtensionCounts PowerTateModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

theorem native_trace_det_at_every_finite_extension {r : Row} [Fact r.prime.Prime]
    (hr : r ∈ printedRows) (L : Type*) [Field L] [Algebra (ZMod r.prime) L]
    [IsAlgClosed L] [DecidableEq L]
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod r.prime) E]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let n := Module.finrank (ZMod r.prime) E
    let F := actual (r := r) L l
    LinearMap.trace ℤ_[l] (Tate l (Points (r := r) L)) (F^n) =
      ((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve r.prime (1 : ZMod r.prime)).baseChange E).toProjective.Point : ℤ)
        : ℤ_[l]) ∧
    LinearMap.det (F^n) = (Fintype.card E : ℤ_[l]) := by
  let n := Module.finrank (ZMod r.prime) E
  have hCount := actual_extension_trace_eq_recurrence (E := E)
    (Paper5PrintedSupersingular.printedRows_prime_at_least_five hr)
    (one_ne_zero : (1 : ZMod r.prime) ≠ 0)
  rw [Paper5PrintedPointCounts.printedRows_actual_firstTrace hr] at hCount
  constructor
  · apply (all_printed_power_traces hr L l hl n).trans
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_one] using
      congrArg (fun z : ℤ => (z : ℤ_[l])) hCount.symm
  · have hq : Fintype.card E = r.prime^n := by
      rw [Module.card_eq_pow_finrank (K := ZMod r.prime) (V := E), ZMod.card]
    rw [hq]
    exact all_printed_power_determinants hr L l hl n

end
end ManuscriptAudit.Paper5OriginalTateExtensionCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper5OriginalTateExtensionCounts.native_trace_det_at_every_finite_extension
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
