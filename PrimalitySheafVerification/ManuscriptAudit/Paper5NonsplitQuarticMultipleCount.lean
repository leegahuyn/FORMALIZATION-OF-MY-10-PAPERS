import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour

/-! Exact actual point counts over extensions of degree divisible by four. -/

namespace ManuscriptAudit.Paper5NonsplitQuarticMultipleCount

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open Paper5NonsplitFrobeniusModFour Paper5NonsplitExtensionRecurrence Paper5PrintedRecurrence
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve paper5_traceCurve_trace_eq_zero)

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- Over the actual degree-4k finite field, the nonsplit centered curve has (p^(2k)−1)² points. -/
theorem quartic_multiple_count (hp : 5 ≤ p) (hr : p % 3 = 2)
    {A : ZMod p} (hA : A ≠ 0) {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod p) E] {k : ℕ} (hd : Module.finrank (ZMod p) E = 4 * k) :
    Nat.card ((Curve A).baseChange E).Point = (p ^ (2 * k) - 1) ^ 2 := by
  have h := actual_extension_trace_eq_recurrence_of_mod_two (E := E) hp hr hA
  have hCard : Fintype.card E = p ^ (4 * k) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hd]
  have hRec : recurrence p 0 (4 * k) = 2 * (p : ℤ) ^ (2 * k) := by
    rw [show 4 * k = 2 * (2 * k) by omega, zero_recurrence_at_even]
    rw [pow_mul (-(p : ℤ)) 2 k, pow_mul (p : ℤ) 2 k, neg_sq]
  rw [paper5_traceCurve_trace_eq_zero hp hr hA, hd, hRec, hCard] at h
  push_cast at h
  have hPow : (p : ℤ) ^ (4 * k) = ((p : ℤ) ^ (2 * k)) ^ 2 := by
    rw [← pow_mul, show 4 * k = (2 * k) * 2 by omega]
  rw [hPow] at h
  have he : (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ) =
      ((p : ℤ) ^ (2 * k) - 1) ^ 2 := by nlinarith
  have hOne : 1 ≤ p ^ (2 * k) := Nat.succ_le_iff.mpr (pow_pos (Fact.out : p.Prime).pos _)
  have hCast : (((p ^ (2 * k) - 1) ^ 2 : ℕ) : ℤ) = ((p : ℤ) ^ (2 * k) - 1) ^ 2 := by
    push_cast [Nat.cast_sub hOne] <;> rfl
  have hc : Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point =
      (p ^ (2 * k) - 1) ^ 2 :=
    Int.ofNat.inj (he.trans hCast.symm)
  rw [printed_eq_centered p A] at hc
  exact (Nat.card_congr (Projective.Point.toAffineAddEquiv
    (W := ((shortCubic (0 : ZMod p) A).baseChange E).toProjective)).symm.toEquiv).trans hc

end
end ManuscriptAudit.Paper5NonsplitQuarticMultipleCount

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5NonsplitQuarticMultipleCount.quartic_multiple_count
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
