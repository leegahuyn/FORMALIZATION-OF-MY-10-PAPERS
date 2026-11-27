import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTorsionAlgebra

/-! The coordinate fibers for ordinary characteristic-thirteen torsion have size twelve. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenTorsionCoordinateCard

open CubicThreeTorsionCard Paper5OrdinaryThirteenAlgebra Paper5OrdinaryThirteenTorsionAlgebra

noncomputable section

variable (K : Type*) [Field K] [CharP K 13]

abbrev QuadraticRoots := {t : K // torsionQuadratic t = 0}

abbrev Coordinates := Σ t : QuadraticRoots K, PowerRoots 3 (t : K) × PowerRoots 2 ((t : K) + 1)

private theorem four_ne_zero : (4 : K) ≠ 0 := numeral_ne_zero 4 (by decide)

private def quadraticEquiv : QuadraticRoots K ≃ PowerRoots 2 (2 : K) where
  toFun t := ⟨4 * (t : K) + 10, (torsionQuadratic_equiv_square _).mp t.property⟩
  invFun u := ⟨((u : K) - 10) / 4, (torsionQuadratic_equiv_square _).mpr (by
    have h : 4 * (((u : K) - 10) / 4) + 10 = (u : K) := by
      field_simp [four_ne_zero K] <;> ring
    rw [h]
    exact u.property)⟩
  left_inv t := Subtype.ext (by
    change (4 * (t : K) + 10 - 10) / 4 = (t : K)
    field_simp [four_ne_zero K] <;> ring)
  right_inv u := Subtype.ext (by
    change 4 * (((u : K) - 10) / 4) + 10 = (u : K)
    field_simp [four_ne_zero K] <;> ring)

variable [IsAlgClosed K] [DecidableEq K]

theorem quadraticRoots_card : Nat.card (QuadraticRoots K) = 2 := by
  exact (Nat.card_congr (quadraticEquiv K)).trans
    (powerRoots_card 2 (2 : K) (by decide) (numeral_ne_zero 2 (by decide))
      (numeral_ne_zero 2 (by decide)))

private theorem xFiber_card (t : QuadraticRoots K) : Nat.card (PowerRoots 3 (t : K)) = 3 :=
  powerRoots_card 3 (t : K) (by decide) (numeral_ne_zero 3 (by decide))
    (torsionQuadratic_nonzero_values t.property).1

private theorem yFiber_card (t : QuadraticRoots K) : Nat.card (PowerRoots 2 ((t : K) + 1)) = 2 :=
  powerRoots_card 2 ((t : K) + 1) (by decide) (numeral_ne_zero 2 (by decide))
    (torsionQuadratic_nonzero_values t.property).2.1

theorem coordinates_card : Nat.card (Coordinates K) = 12 := by
  letI : Finite (QuadraticRoots K) := Nat.finite_of_card_ne_zero (by rw [quadraticRoots_card]; decide)
  letI : Fintype (QuadraticRoots K) := Fintype.ofFinite _
  letI (t : QuadraticRoots K) : Finite (PowerRoots 3 (t : K)) :=
    Nat.finite_of_card_ne_zero (by rw [xFiber_card]; decide)
  letI (t : QuadraticRoots K) : Finite (PowerRoots 2 ((t : K) + 1)) :=
    Nat.finite_of_card_ne_zero (by rw [yFiber_card]; decide)
  letI (t : QuadraticRoots K) : Fintype (PowerRoots 3 (t : K)) := Fintype.ofFinite _
  letI (t : QuadraticRoots K) : Fintype (PowerRoots 2 ((t : K) + 1)) := Fintype.ofFinite _
  calc
    Nat.card (Coordinates K) = ∑ t : QuadraticRoots K,
        Nat.card (PowerRoots 3 (t : K) × PowerRoots 2 ((t : K) + 1)) := by
      simp only [Coordinates, Nat.card_eq_fintype_card, Fintype.card_sigma]
    _ = ∑ _t : QuadraticRoots K, 6 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.card_prod, xFiber_card, yFiber_card]
    _ = _ := by simp [← Nat.card_eq_fintype_card, quadraticRoots_card]

end
end ManuscriptAudit.Paper5OrdinaryThirteenTorsionCoordinateCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionCoordinateCard.quadraticRoots_card,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionCoordinateCard.coordinates_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
