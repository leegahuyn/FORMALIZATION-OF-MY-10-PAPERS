import Lean.Util.CollectAxioms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTorsionAlgebra

/-! The coordinate fibers for ordinary characteristic-nineteen torsion have size eighteen. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinateCard

open CubicThreeTorsionCard Paper5OrdinaryNineteenAlgebra Paper5OrdinaryNineteenTorsionAlgebra

noncomputable section

variable (K : Type*) [Field K] [CharP K 19]

abbrev CubicRoots := {t : K // torsionCubic t = 0}

abbrev Coordinates := Σ t : CubicRoots K, PowerRoots 3 (t : K) × PowerRoots 2 ((t : K) + 1)

private def rootValue : Fin 3 → K := ![2, 14, 17]

private theorem rootValue_mem (i : Fin 3) : torsionCubic (rootValue K i) = 0 := by
  fin_cases i <;> simp [rootValue, torsionCubic]

private theorem rootValue_injective : Function.Injective (rootValue K) := by
  have h₂₁₄ : (2 : K) ≠ 14 := fun h =>
    numeral_ne_zero 12 (by decide) (by linear_combination -h)
  have h₂₁₇ : (2 : K) ≠ 17 := fun h =>
    numeral_ne_zero 15 (by decide) (by linear_combination -h)
  have h₁₄₁₇ : (14 : K) ≠ 17 := fun h =>
    numeral_ne_zero 3 (by decide) (by linear_combination -h)
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp [rootValue, h₂₁₄, Ne.symm h₂₁₄, h₂₁₇, Ne.symm h₂₁₇, h₁₄₁₇, Ne.symm h₁₄₁₇] at he ⊢

private def rootEquiv : Fin 3 ≃ CubicRoots K :=
  Equiv.ofBijective (fun i => ⟨rootValue K i, rootValue_mem K i⟩) (by
    constructor
    · intro i j h
      exact rootValue_injective K (congrArg Subtype.val h)
    · intro t
      rcases (torsionCubic_eq_zero_iff (t : K)).mp t.property with he | he | he
      · exact ⟨0, Subtype.ext he.symm⟩
      · exact ⟨1, Subtype.ext he.symm⟩
      · exact ⟨2, Subtype.ext he.symm⟩)

theorem cubicRoots_card : Nat.card (CubicRoots K) = 3 :=
  (Nat.card_congr (rootEquiv K)).symm.trans (by simp)

variable [IsAlgClosed K] [DecidableEq K]

private theorem xFiber_card (t : CubicRoots K) : Nat.card (PowerRoots 3 (t : K)) = 3 :=
  powerRoots_card 3 (t : K) (by decide) (numeral_ne_zero 3 (by decide))
    (torsionCubic_nonzero_values t.property).1

private theorem yFiber_card (t : CubicRoots K) : Nat.card (PowerRoots 2 ((t : K) + 1)) = 2 :=
  powerRoots_card 2 ((t : K) + 1) (by decide) (numeral_ne_zero 2 (by decide))
    (torsionCubic_nonzero_values t.property).2.1

theorem coordinates_card : Nat.card (Coordinates K) = 18 := by
  letI : Finite (CubicRoots K) := Nat.finite_of_card_ne_zero (by rw [cubicRoots_card]; decide)
  letI : Fintype (CubicRoots K) := Fintype.ofFinite _
  letI (t : CubicRoots K) : Finite (PowerRoots 3 (t : K)) :=
    Nat.finite_of_card_ne_zero (by rw [xFiber_card]; decide)
  letI (t : CubicRoots K) : Finite (PowerRoots 2 ((t : K) + 1)) :=
    Nat.finite_of_card_ne_zero (by rw [yFiber_card]; decide)
  letI (t : CubicRoots K) : Fintype (PowerRoots 3 (t : K)) := Fintype.ofFinite _
  letI (t : CubicRoots K) : Fintype (PowerRoots 2 ((t : K) + 1)) := Fintype.ofFinite _
  calc
    Nat.card (Coordinates K) = ∑ t : CubicRoots K,
        Nat.card (PowerRoots 3 (t : K) × PowerRoots 2 ((t : K) + 1)) := by
      simp only [Coordinates, Nat.card_eq_fintype_card, Fintype.card_sigma]
    _ = ∑ _t : CubicRoots K, 6 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.card_prod, xFiber_card, yFiber_card]
    _ = _ := by simp [← Nat.card_eq_fintype_card, cubicRoots_card]

end
end ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinateCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinateCard.cubicRoots_card,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinateCard.coordinates_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
