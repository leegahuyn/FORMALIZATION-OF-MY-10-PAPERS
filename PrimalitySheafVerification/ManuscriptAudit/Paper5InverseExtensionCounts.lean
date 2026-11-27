import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedInverseTatePowers
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedActualExtensionCounts

/-! Exact inverse point-Frobenius coefficients at every extension of the original good rows. -/

namespace ManuscriptAudit.Paper5InverseExtensionCounts

open PowerTateModule Paper5PrintedRecurrence Paper5AllPrintedInverseTate
open Paper5PrintedInverseTatePowers Paper5PrintedActualExtensionCounts
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

theorem inverse_trace_det_at_every_finite_extension {r : Row} [Fact r.prime.Prime]
    (hr : r ∈ printedRows) (L : Type*) [Field L] [Algebra (ZMod r.prime) L]
    [IsAlgClosed L] [DecidableEq L]
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod r.prime) E]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let n := Module.finrank (ZMod r.prime) E
    let F := inverseAction L l hr hl
    LinearMap.trace ℚ_[l] (RationalRowTate (r := r) L l) (F^n) =
      ((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve r.prime (1 : ZMod r.prime)).baseChange E).toProjective.Point : ℤ)
        : ℚ_[l]) / (Fintype.card E : ℚ_[l]) ∧
    LinearMap.det (F^n) = (Fintype.card E : ℚ_[l])⁻¹ := by
  let n := Module.finrank (ZMod r.prime) E
  have hCount := actual_extension_trace_eq_recurrence (E := E)
    (Paper5PrintedSupersingular.printedRows_prime_at_least_five hr)
    (one_ne_zero : (1 : ZMod r.prime) ≠ 0)
  rw [Paper5PrintedPointCounts.printedRows_actual_firstTrace hr] at hCount
  have hq : Fintype.card E = r.prime^n := by
    rw [Module.card_eq_pow_finrank (K := ZMod r.prime) (V := E), ZMod.card]
  constructor
  · have h := inverse_power_trace L l hr hl n
    rw [← hCount, ← hq] at h
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_one] using h
  · rw [hq]
    exact inverse_power_det L l hr hl n

end
end ManuscriptAudit.Paper5InverseExtensionCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper5InverseExtensionCounts.inverse_trace_det_at_every_finite_extension
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
