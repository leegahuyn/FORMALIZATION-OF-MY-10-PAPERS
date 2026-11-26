import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5FrobeniusModTwo
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusModTwoRecurrence

/-! Actual Frobenius trace powers modulo two and the six printed columns. -/

namespace ManuscriptAudit.Paper5FrobeniusParity

open WeierstrassCurve CubicTrace Paper5FrobeniusModTwo Paper5ActualHasseWeil
open WeierstrassFrobeniusTwoTorsionTrace FrobeniusModTwoLinear FrobeniusModTwoRecurrence
open Paper5PrintedRecurrence

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

private def torsionBasis (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) :
    Module.Basis (Fin 2) (ZMod 2) (geometricTwoTorsion p L (printedAffine p A)) := by
  have h := geometricTwoTorsion_card p L hp hA
  letI : Finite (geometricTwoTorsion p L (printedAffine p A)) :=
    Nat.finite_of_card_ne_zero (by rw [h]; decide)
  exact basisOfCardFour _ h

theorem actualFrobenius_trace_power_eq_point_count (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E] :
    LinearMap.trace (ZMod 2) (geometricTwoTorsion p L (printedAffine p A))
      ((actualFrobenius p L hp hA).toLinearMap ^ Module.finrank (ZMod p) E) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve p A).baseChange E).toProjective.Point : ℤ)) : ZMod 2) := by
  rw [Paper5PrintedActualExtensionCounts.actual_extension_trace_eq_recurrence hp hA]
  exact trace_pow_eq_recurrence_mod_two _ (torsionBasis p L hp hA)
    (actualFrobenius p L hp hA) p (firstTrace p A)
    (actualFrobenius_trace p L hp hA) (actualFrobenius_det p L hp hA) _

end

section Table

variable {r : Row} [Fact r.prime.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]

theorem printedRows_actual_frobenius_trace_powers (hr : r ∈ printedRows) :
    ((List.range 6).map fun i =>
      LinearMap.trace (ZMod 2) (geometricTwoTorsion r.prime L (printedAffine r.prime 1))
        ((actualFrobenius r.prime L
          (Paper5PrintedSupersingular.printedRows_prime_at_least_five hr)
          (one_ne_zero : (1 : ZMod r.prime) ≠ 0)).toLinearMap ^ (i + 1))) =
          r.traceColumns.map (fun a : ℤ => (a : ZMod 2)) := by
  let hp := Paper5PrintedSupersingular.printedRows_prime_at_least_five hr
  let hA : (1 : ZMod r.prime) ≠ 0 := one_ne_zero
  have hTrace : firstTrace r.prime (1 : ZMod r.prime) = r.a1 :=
    Paper5PrintedPointCounts.printedRows_actual_firstTrace hr
  have ha := actualFrobenius_trace r.prime L hp hA
  rw [hTrace] at ha
  exact printed_columns_mod_two _ (torsionBasis r.prime L hp hA)
    (actualFrobenius r.prime L hp hA) hr ha (actualFrobenius_det r.prime L hp hA)

end Table
end ManuscriptAudit.Paper5FrobeniusParity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5FrobeniusParity.actualFrobenius_trace_power_eq_point_count,
      ``ManuscriptAudit.Paper5FrobeniusParity.printedRows_actual_frobenius_trace_powers] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
