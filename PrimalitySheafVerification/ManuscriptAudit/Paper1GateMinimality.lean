import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice

/-! Pairwise separation gives a weaker condition than irredundance of the full meet. -/

namespace ManuscriptAudit.Paper1GateMinimality

/-- Removing one gate strictly increases the accepted set exactly when all other gates accept one
input rejected by the removed gate. -/
theorem strict_removal_iff {I α : Type*} (gate : I → α → Prop) (i : I) :
    {a : α | ∀ j, gate j a} ⊂ {a : α | ∀ j, j ≠ i → gate j a} ↔
      ∃ a, (∀ j, j ≠ i → gate j a) ∧ ¬ gate i a := by
  classical
  change ({a : α | ∀ j, gate j a} : Set α) < {a : α | ∀ j, j ≠ i → gate j a} ↔ _
  rw [lt_iff_le_not_ge]
  constructor
  · rintro ⟨_, hn⟩
    by_contra! h
    apply hn
    intro a ha
    change ∀ j, gate j a
    intro j
    by_cases hj : j = i
    · subst j
      exact h a ha
    · exact ha j hj
  · rintro ⟨a, ha, hno⟩
    exact ⟨fun _ hx j _ => hx j, fun h => hno (h ha i)⟩

/-- The accepted inputs comprise one universal input and one input for each single gate. -/
def accepts (i : Fin 4) (a : Option (Fin 4)) : Prop :=
  a = none ∨ a = some i

theorem every_ordered_pair_separated (i j : Fin 4) (h : i ≠ j) :
    ∃ a, accepts i a ∧ ¬ accepts j a := by
  refine ⟨some i, Or.inr rfl, ?_⟩
  simp [accepts, h]

private theorem accepts_none_of_two {i j : Fin 4} (hij : i ≠ j)
    {a : Option (Fin 4)} (hi : accepts i a) (hj : accepts j a) : a = none := by
  rcases hi with h | h
  · exact h
  · rw [h] at hj
    simp [accepts, hij] at hj

theorem every_single_gate_redundant (i : Fin 4) :
    {a | ∀ j, accepts j a} = {a | ∀ j, j ≠ i → accepts j a} := by
  ext a
  change (∀ j, accepts j a) ↔ (∀ j, j ≠ i → accepts j a)
  constructor
  · intro h j _
    exact h j
  · intro h j
    apply Or.inl
    by_cases h0 : i = 0
    · subst i
      exact accepts_none_of_two (i := 1) (j := 2) (by decide)
        (h 1 (by decide)) (h 2 (by decide))
    · by_cases h1 : i = 1
      · subst i
        exact accepts_none_of_two (i := 0) (j := 2) (by decide)
          (h 0 (by decide)) (h 2 (by decide))
      · exact accepts_none_of_two (i := 0) (j := 1) (by decide)
          (h 0 (Ne.symm h0)) (h 1 (Ne.symm h1))

end ManuscriptAudit.Paper1GateMinimality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper1GateMinimality.strict_removal_iff,
      ``ManuscriptAudit.Paper1GateMinimality.every_ordered_pair_separated,
      ``ManuscriptAudit.Paper1GateMinimality.every_single_gate_redundant] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
