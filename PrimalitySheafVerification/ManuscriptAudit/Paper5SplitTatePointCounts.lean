import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5ExtensionRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenPrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenPrintedTrace

/-! Native split Tate power traces agree with the actual extension point counts once their
degree-one trace and determinant are known. -/

namespace ManuscriptAudit.Paper5SplitTatePointCounts

open Module Paper5LinearTraceRecurrence Paper5ExtensionRecurrence Paper5PrintedPointCounts
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

/-- A rank-two action with the exact arithmetic coefficients gives the actual projective point
count over every finite extension of a split prime field. -/
theorem trace_power_eq_extension_count {p : ℕ} [Fact p.Prime]
    {E R V : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    [CommRing R] [Nontrivial R] [AddCommGroup V] [Module R V]
    (hp : 5 ≤ p) (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0)
    (B : Basis (Fin 2) R V) (F : Module.End R V)
    (ht : LinearMap.trace R V F =
      (((p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ) : ℤ) : R))
    (hd : LinearMap.det F = (p : R)) :
    LinearMap.trace R V (F ^ (Module.finrank (ZMod p) E)) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ) : ℤ) : R) := by
  let ap : ℤ := (p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ)
  have h := actual_extension_trace_eq_recurrence (E := E) hp hs hA
  exact (trace_pow_eq_recurrence B F p ap ht hd _).trans
    (congrArg (fun z : ℤ => (z : R)) h.symm)

section Seven

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod 7) E]
variable (l : ℕ) [Fact l.Prime]

open Paper5OrdinarySevenOneTate Paper5OrdinarySevenPrintedTrace

theorem seven_trace_eq_extension_count (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (PowerTateModule.Tate l (Geometric L))
      (action L l ^ Module.finrank (ZMod 7) E) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve 7 (1 : ZMod 7)).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  obtain ⟨ht, hd⟩ := trace_det L l hl
  have h₁ := printedRows_actual_firstTrace sevenRow_mem
  change (7 : ℤ) + 1 - (Nat.card (paper5TraceCurve 7 (1 : ZMod 7)).toProjective.Point : ℤ) = -4 at h₁
  refine trace_power_eq_extension_count (E := E) (by decide) (by decide) one_ne_zero
    (tateBasis L l hl) (action L l) ?_ (by simpa only [Nat.cast_ofNat] using hd)
  rw [h₁]
  simpa only [Int.cast_neg, Int.cast_ofNat] using ht

end Seven

section Thirteen

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 13) L] [CharP L 13] [IsAlgClosed L] [DecidableEq L]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod 13) E]
variable (l : ℕ) [Fact l.Prime]

open Paper5OrdinaryThirteenCoordinates Paper5OrdinaryThirteenTate Paper5OrdinaryThirteenPrintedTrace

theorem thirteen_trace_eq_extension_count (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (PowerTateModule.Tate l (Points L))
      (action L l ^ Module.finrank (ZMod 13) E) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve 13 (1 : ZMod 13)).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  exact trace_power_eq_extension_count (E := E) (by decide) (by decide) one_ne_zero
    (tateBasis L l hl) (action L l) (trace_eq_signed_count L l hl)
    (by simpa only [Nat.cast_ofNat] using (trace_det L l hl).2)

end Thirteen

end
end ManuscriptAudit.Paper5SplitTatePointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5SplitTatePointCounts.trace_power_eq_extension_count,
      ``ManuscriptAudit.Paper5SplitTatePointCounts.seven_trace_eq_extension_count,
      ``ManuscriptAudit.Paper5SplitTatePointCounts.thirteen_trace_eq_extension_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
