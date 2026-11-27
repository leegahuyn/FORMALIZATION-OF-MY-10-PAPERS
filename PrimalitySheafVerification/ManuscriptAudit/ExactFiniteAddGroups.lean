import Lean.Util.CollectAxioms
import Mathlib.Algebra.Exact.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Cardinalities detect injectivity at the beginning of a finite exact sequence. -/

namespace ManuscriptAudit.ExactFiniteAddGroups

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Finite A] [Finite B] [Finite C]

/-- If the middle cardinality is the product of the end cardinalities,
the first map in an exact sequence with surjective second map is injective. -/
theorem first_injective (f : A →+ B) (g : B →+ C) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hCard : Nat.card B = Nat.card C * Nat.card A) :
    Function.Injective f := by
  classical
  let q := QuotientAddGroup.quotientKerEquivOfSurjective g hg
  have hB : Nat.card B = Nat.card C * Nat.card g.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, Nat.card_congr q.toEquiv]
  have hA : Nat.card A = Nat.card g.ker :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hCard.symm.trans hB)
  let fK : A → g.ker := fun a ↦ ⟨f a, (hfg (f a)).mpr ⟨a, rfl⟩⟩
  have hK : Function.Surjective fK := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := (hfg x).mp hx
    exact ⟨a, Subtype.ext ha⟩
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite g.ker
  let e : A ≃ g.ker := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using hA)
  have hfK := hK.injective_of_finite e
  intro x y h
  exact hfK (Subtype.ext h)

end ManuscriptAudit.ExactFiniteAddGroups

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExactFiniteAddGroups.first_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
