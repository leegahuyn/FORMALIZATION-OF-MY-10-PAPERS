import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGoodReductionFrobeniusModTwo
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusExtensionTrace

/-! The actual finite-extension traces of every good short cubic satisfy the recurrence modulo two. -/

namespace ManuscriptAudit.CubicGoodReductionPointCountsModTwo

open FiniteFieldPointCount WeierstrassFrobeniusTwoTorsionTrace
open CubicGoodReductionFrobeniusModTwo Paper5PrintedRecurrence

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] [DecidableEq E]

/-- The native point count obeys the printed recurrence after reduction modulo two. -/
theorem extension_trace_eq_recurrence (hpTwo : p ≠ 2) {c A : ZMod p}
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    (((Fintype.card E : ℤ) + 1 -
      (Nat.card ((shortCubic c A).toProjective.baseChange E).Point : ℤ)) : ZMod 2) =
      (recurrence p (arithmeticTrace p c A) (Module.finrank (ZMod p) E) : ZMod 2) := by
  let W := (shortCubic c A).toProjective
  let V := geometricTwoTorsion p L W.toAffine
  have hcard : Nat.card V = 4 := geometricTwoTorsion_card p L hpTwo hΔ
  letI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let b : Module.Basis (Fin 2) (ZMod 2) V :=
    FrobeniusModTwoLinear.basisOfCardFour V hcard
  rw [← WeierstrassFrobeniusExtensionTrace.projective_trace_pow_eq_signed_point_count_of_isAlgClosed
    p L E W hcard hpTwo]
  exact FrobeniusModTwoRecurrence.trace_pow_eq_recurrence_mod_two V b
    (frobeniusOfCardFour p L W.toAffine hcard) p (arithmeticTrace p c A)
    (actualFrobenius_trace p L hpTwo hΔ) (actualFrobenius_det p L hpTwo hΔ) _

end
end ManuscriptAudit.CubicGoodReductionPointCountsModTwo

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicGoodReductionPointCountsModTwo.extension_trace_eq_recurrence
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
