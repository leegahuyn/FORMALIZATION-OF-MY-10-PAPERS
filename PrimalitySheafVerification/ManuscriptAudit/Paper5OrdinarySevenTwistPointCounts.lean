import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenTwistTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts

/-! Exact rational point counts for all six ordinary characteristic-seven twists. -/

namespace ManuscriptAudit.Paper5OrdinarySevenTwistPointCounts

open Paper5OrdinarySevenTwistParameters Paper5OrdinarySevenTwistTate
open Paper5PrintedPointCounts PowerTateModule
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem checked_counts : ∀ A : ZMod 7, A ≠ 0 →
    (row A).trace = 8 - (enumeratedPointsFor 7 A.val : ℤ) := by decide

/-- The exact trace table agrees with the native projective point counts over F₇. -/
theorem signed_count (A : ZMod 7) (hA : A ≠ 0) :
    (row A).trace = 8 - (Nat.card (paper5TraceCurve 7 A).toProjective.Point : ℤ) := by
  have hA' : (A.val : ZMod 7) ≠ 0 := by simpa only [ZMod.natCast_zmod_val] using hA
  have hc : Nat.card (paper5TraceCurve 7 A).toProjective.Point = enumeratedPointsFor 7 A.val := by
    simpa only [ZMod.natCast_zmod_val] using
      projective_count_eq_enumeratedFor (p := 7) (A := A.val) (by decide) hA'
  rw [hc]
  exact checked_counts A hA

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

theorem actual_trace_eq_signed_count (hl : l = 2 ∨ l = 3) (A : ZMod 7) (hA : A ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric L A)) (action L l A) =
      ((8 - (Nat.card (paper5TraceCurve 7 A).toProjective.Point : ℤ) : ℤ) : ℤ_[l]) :=
  (trace_det L l hl A hA).1.trans (congrArg (fun z : ℤ => (z : ℤ_[l])) (signed_count A hA))

end
end ManuscriptAudit.Paper5OrdinarySevenTwistPointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenTwistPointCounts.signed_count,
      ``ManuscriptAudit.Paper5OrdinarySevenTwistPointCounts.actual_trace_eq_signed_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
