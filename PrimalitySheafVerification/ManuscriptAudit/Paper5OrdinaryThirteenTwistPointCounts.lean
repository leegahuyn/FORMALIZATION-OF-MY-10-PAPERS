import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTwistTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5SplitTatePointCounts

/-! Exact rational point counts for all twelve ordinary characteristic-thirteen twists. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenTwistPointCounts

open Paper5OrdinaryThirteenTwistParameters Paper5OrdinaryThirteenTwistTate
open Paper5PrintedPointCounts PowerTateModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem checked_counts : ∀ A : ZMod 13, A ≠ 0 →
    (row A).trace = 14 - (enumeratedPointsFor 13 A.val : ℤ) := by decide

/-- The exact trace table agrees with the native projective point counts over F₁₃. -/
theorem signed_count (A : ZMod 13) (hA : A ≠ 0) :
    (row A).trace = 14 - (Nat.card (paper5TraceCurve 13 A).toProjective.Point : ℤ) := by
  have hA' : (A.val : ZMod 13) ≠ 0 := by simpa only [ZMod.natCast_zmod_val] using hA
  have hc : Nat.card (paper5TraceCurve 13 A).toProjective.Point = enumeratedPointsFor 13 A.val := by
    simpa only [ZMod.natCast_zmod_val] using
      projective_count_eq_enumeratedFor (p := 13) (A := A.val) (by decide) hA'
  rw [hc]
  exact checked_counts A hA

variable (L : Type*) [Field L] [Algebra (ZMod 13) L] [CharP L 13] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

theorem actual_trace_eq_signed_count (hl : l = 2 ∨ l = 3) (A : ZMod 13) (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric L A)) (action L l A) =
      ((14 - (Nat.card (paper5TraceCurve 13 A).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) :=
  (trace_det L l hl A hA).1.trans (congrArg (fun z : ℤ => (z : ℤ_[l])) (signed_count A hA))

theorem actual_trace_eq_extension_count
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod 13) E]
    (hl : l = 2 ∨ l = 3) (A : ZMod 13) (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric L A)) (action L l A ^ Module.finrank (ZMod 13) E) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve 13 A).baseChange E).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) := by
  exact Paper5SplitTatePointCounts.trace_power_eq_extension_count (E := E)
    (by decide) (by decide) hA (tateBasis L l hl A hA) (action L l A)
    (actual_trace_eq_signed_count L l hl A hA)
    (by simpa only [Nat.cast_ofNat] using (trace_det L l hl A hA).2)

end
end ManuscriptAudit.Paper5OrdinaryThirteenTwistPointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenTwistPointCounts.signed_count,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTwistPointCounts.actual_trace_eq_signed_count,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTwistPointCounts.actual_trace_eq_extension_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
