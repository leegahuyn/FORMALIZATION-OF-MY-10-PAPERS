import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitPrimeAdicExtensionTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedSupersingular

/-! The six native Tate traces at every nonsplit prime represented in Paper 5. -/

namespace ManuscriptAudit.Paper5PrintedNonsplitTateTraces

open PrimalitySheafVerification.ManuscriptAudit (paper5_traceCurve_trace_eq_zero)
open CubicNonsplitThreeAdicTrace CubicNonsplitPrimeAdicFrobenius CubicNonsplitTwoThreeAdicCharpoly
open PowerTateModule Paper5PrintedRecurrence Paper5PrintedPointCounts Paper5PrintedSupersingular
open Paper5NonsplitFrobeniusModFour Paper5LinearTraceRecurrence Module

noncomputable section

variable {r : Row} [Fact r.prime.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

abbrev Points := GeometricPoints (ZMod r.prime) L (1 : ZMod r.prime)
abbrev actual : Module.End ℤ_[l] (Tate l (Points (r := r) L)) :=
  Action (ZMod r.prime) L l (1 : ZMod r.prime)

/-- A rank-two native action with the printed coefficients gives all six printed traces. -/
theorem six_of_coefficients (hr : r ∈ printedRows)
    (B : Basis (Fin 2) ℤ_[l] (Tate l (Points (r := r) L)))
    (ht : LinearMap.trace ℤ_[l] (Tate l (Points (r := r) L)) (actual (r := r) L l) = (r.a1 : ℤ_[l]))
    (hd : LinearMap.det (actual (r := r) L l) = (r.prime : ℤ_[l])) :
    (List.range 6).map (fun i =>
      LinearMap.trace ℤ_[l] (Tate l (Points (r := r) L)) (actual (r := r) L l ^ (i + 1))) =
      r.traceColumns.map (fun a : ℤ => (a : ℤ_[l])) := by
  rw [printedRows_recurrence hr, Row.recurrenceColumns, List.map_map]
  apply congrArg (fun f : ℕ → ℤ_[l] => (List.range 6).map f)
  funext i
  exact trace_pow_eq_recurrence B (actual (r := r) L l) r.prime r.a1 ht hd (i + 1)

private def basis (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3) :
    Basis (Fin 2) ℤ_[l] (Tate l (Points (r := r) L)) := by
  obtain ⟨h₂, h₃⟩ := small_char r.prime (ZMod r.prime) (printedRows_prime_at_least_five hr)
  apply Classical.choice
  rcases hl with rfl | rfl
  · exact ⟨twoAdicBasis (ZMod r.prime) L h₂ h₃ (one_ne_zero : (1 : ZMod r.prime) ≠ 0)⟩
  · exact ⟨threeAdicBasis (ZMod r.prime) L h₂ h₃ (one_ne_zero : (1 : ZMod r.prime) ≠ 0)⟩

/-- All nonsplit printed rows agree with the actual Tate powers at both coefficient primes. -/
theorem six_nonsplit (hr : r ∈ printedRows) (hn : r.prime % 3 = 2) (hl : l = 2 ∨ l = 3) :
    (List.range 6).map (fun i =>
      LinearMap.trace ℤ_[l] (Tate l (Points (r := r) L)) (actual (r := r) L l ^ (i + 1))) =
      r.traceColumns.map (fun a : ℤ => (a : ℤ_[l])) := by
  let E := ZMod r.prime
  have hp := printedRows_prime_at_least_five hr
  obtain ⟨h₂, h₃⟩ := small_char r.prime E hp
  have hq : Fintype.card E % 3 = 2 := by simpa only [E, ZMod.card] using hn
  have hA : (1 : E) ≠ 0 := one_ne_zero
  have hr0 : r.a1 = 0 :=
    (printedRows_actual_firstTrace hr).symm.trans (paper5_traceCurve_trace_eq_zero hp hn hA)
  have ht := actual_prime_adic_trace_zero E L l h₂ h₃ hA hq
  refine six_of_coefficients L l hr (basis L l hr hl) ?_ ?_
  · simpa only [hr0, Int.cast_zero] using ht
  · rcases hl with rfl | rfl
    · simpa only [E, ZMod.card] using two_adic_determinant E L h₂ h₃ hA hq
    · simpa only [E, ZMod.card] using three_adic_determinant E L h₂ h₃ hA hq

end
end ManuscriptAudit.Paper5PrintedNonsplitTateTraces

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5PrintedNonsplitTateTraces.six_of_coefficients,
      ``ManuscriptAudit.Paper5PrintedNonsplitTateTraces.six_nonsplit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
