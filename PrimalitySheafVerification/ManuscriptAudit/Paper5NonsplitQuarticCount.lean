import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour

/-! Actual nonsplit centered-cubic point count over a quartic field extension. -/

namespace ManuscriptAudit.Paper5NonsplitQuarticCount

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open Paper5NonsplitFrobeniusModFour Paper5NonsplitExtensionRecurrence Paper5PrintedRecurrence
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve paper5_traceCurve_trace_eq_zero)

noncomputable section

variable (p : ℕ) [Fact p.Prime]

theorem quartic_count (hp : 5 ≤ p) (hr : p % 3 = 2)
    {A : ZMod p} (hA : A ≠ 0) {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] (hd : Module.finrank (ZMod p) E = 4) :
    Nat.card ((Curve A).baseChange E).Point = (p ^ 2 - 1) ^ 2 := by
  have h := actual_extension_trace_eq_recurrence_of_mod_two (E := E) hp hr hA
  have hCard : Fintype.card E = p ^ 4 := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hd]
  have hRec : recurrence p 0 4 = 2 * (p : ℤ) ^ 2 := by
    calc
      _ = 2 * (-(p : ℤ)) ^ 2 := zero_recurrence_at_even p 2
      _ = _ := by ring
  rw [paper5_traceCurve_trace_eq_zero hp hr hA, hd, hRec, hCard] at h
  push_cast at h
  have he : (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ) =
      ((p : ℤ) ^ 2 - 1) ^ 2 := by nlinarith
  have hOne : 1 ≤ p ^ 2 := Nat.succ_le_iff.mpr (pow_pos (Fact.out : p.Prime).pos 2)
  have hCast : (((p ^ 2 - 1) ^ 2 : ℕ) : ℤ) = ((p : ℤ) ^ 2 - 1) ^ 2 := by
    push_cast [Nat.cast_sub hOne]
  have hc : Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point = (p ^ 2 - 1) ^ 2 :=
    Int.ofNat.inj (he.trans hCast.symm)
  rw [printed_eq_centered p A] at hc
  exact (Nat.card_congr (Projective.Point.toAffineAddEquiv
    (W := ((shortCubic (0 : ZMod p) A).baseChange E).toProjective)).symm.toEquiv).trans hc

end
end ManuscriptAudit.Paper5NonsplitQuarticCount

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper5NonsplitQuarticCount.quartic_count
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
