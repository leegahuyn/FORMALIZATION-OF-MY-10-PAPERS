import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic

/-! Finite cardinal bounds for two consecutive binary labels. -/

namespace ManuscriptAudit.BinaryExactCardinality

noncomputable section

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

private theorem binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) a

/-- If the kernel of a binary-valued map is covered by a binary subgroup,
the ambient group has at most four elements. -/
theorem finite_card_le_four (δ : ZMod 2 →+ G) (p : G →+ ZMod 2)
    (h : ∀ x, p x = 0 → ∃ a, δ a = x) :
    Finite G ∧ Nat.card G ≤ 4 := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : G, p w = 1 ∨ ∀ x, p x = 0 := by
    by_cases he : ∃ w : G, p w = 1
    · exact he.imp fun _ hw => Or.inl hw
    · refine ⟨0, Or.inr (fun x => ?_)⟩
      exact (binary_cases (p x)).resolve_right (fun hx => he ⟨x, hx⟩)
  let f : (ZMod 2 × ZMod 2) → G := fun a => δ a.1 + (if a.2 = 0 then 0 else w)
  have hf : Function.Surjective f := by
    intro x
    by_cases hx : p x = 0
    · obtain ⟨a, ha⟩ := h x hx
      exact ⟨(a, 0), by simp [f, ha]⟩
    · have hp : p x = 1 := (binary_cases (p x)).resolve_left hx
      have hwp : p w = 1 := hw.resolve_right (fun h₀ => hx (h₀ x))
      have hz : p (x - w) = 0 := by rw [map_sub, hp, hwp, sub_self]
      obtain ⟨a, ha⟩ := h (x - w) hz
      exact ⟨(a, 1), by simp [f, ha]⟩
  letI : Finite G := Finite.of_surjective f hf
  letI : Fintype G := Fintype.ofFinite G
  refine ⟨inferInstance, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card] using
    Fintype.card_le_of_surjective f hf

/-- Two nonzero classes are independent for counting when a homomorphism
kills one and detects the other. -/
theorem four_le_card [Finite G] (p : G →+ H) (a b : G)
    (ha : a ≠ 0) (hp : p a = 0) (hb : p b ≠ 0) : 4 ≤ Nat.card G := by
  classical
  let select (g : G) (x : ZMod 2) : G := if x = 0 then 0 else g
  have hsel (g : G) (hg : g ≠ 0) : Function.Injective (select g) := by
    intro x y h
    rcases binary_cases x with rfl | rfl <;> rcases binary_cases y with rfl | rfl
    · rfl
    · exact (hg (by simpa [select] using h.symm)).elim
    · exact (hg (by simpa [select] using h)).elim
    · rfl
  have hs (g : G) (x : ZMod 2) : p (select g x) = if x = 0 then 0 else p g := by
    by_cases hx : x = 0 <;> simp [select, hx]
  let f : (ZMod 2 × ZMod 2) → G := fun w => select a w.1 + select b w.2
  have hi : Function.Injective f := by
    intro x y h
    have h₂ : x.2 = y.2 := by
      have E := congrArg p h
      change p (select a x.1 + select b x.2) = p (select a y.1 + select b y.2) at E
      have h₀ (z : ZMod 2) : p (select a z) = 0 := by simp [hs, hp]
      simp only [map_add, h₀, zero_add, hs] at E
      rcases binary_cases x.2 with hx | hx <;> rcases binary_cases y.2 with hy | hy
      · exact hx.trans hy.symm
      · rw [hx, hy, if_pos rfl, if_neg one_ne_zero] at E
        exact (hb E.symm).elim
      · rw [hx, hy, if_neg one_ne_zero, if_pos rfl] at E
        exact (hb E).elim
      · exact hx.trans hy.symm
    apply Prod.ext _ h₂
    apply hsel a ha
    change select a x.1 + select b x.2 = select a y.1 + select b y.2 at h
    rw [h₂] at h
    exact add_right_cancel h
  letI : Fintype G := Fintype.ofFinite G
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card] using
    Fintype.card_le_of_injective f hi

end
end ManuscriptAudit.BinaryExactCardinality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.BinaryExactCardinality.finite_card_le_four,
      ``ManuscriptAudit.BinaryExactCardinality.four_le_card] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
