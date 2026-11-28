import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-! The two base-change maps into the fixed double cover form
the actual self-pushout over every refining base. -/

namespace ManuscriptAudit.AffineStageFixedCoproductSquare

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C] [HasBinaryCoproducts C]

private def left (B E : C) : B ⨿ E ⟶ B ⨿ (E ⨿ E) :=
  coprod.map (𝟙 B) coprod.inl

private def right (B E : C) : B ⨿ E ⟶ B ⨿ (E ⨿ E) :=
  coprod.map (𝟙 B) coprod.inr

private theorem condition (B E : C) :
    (coprod.inl : B ⟶ B ⨿ E) ≫ left B E = coprod.inl ≫ right B E := by
  simp [left, right]

private def desc {B E : C}
    (s : PushoutCocone (coprod.inl : B ⟶ B ⨿ E) (coprod.inl : B ⟶ B ⨿ E)) :
    B ⨿ (E ⨿ E) ⟶ s.pt :=
  coprod.desc (coprod.inl ≫ s.inl)
    (coprod.desc (coprod.inr ≫ s.inl) (coprod.inr ≫ s.inr))

/-- Base change of the original cover's self-pushout is the
self-pushout of the base-changed cover. -/
theorem isPushout (B E : C) :
    IsPushout (coprod.inl : B ⟶ B ⨿ E) coprod.inl
      (coprod.map (𝟙 B) (coprod.inl : E ⟶ E ⨿ E))
      (coprod.map (𝟙 B) (coprod.inr : E ⟶ E ⨿ E)) := by
  change IsPushout _ _ (left B E) (right B E)
  apply IsPushout.of_isColimit' ⟨condition B E⟩
  refine PushoutCocone.IsColimit.mk _ desc ?_ ?_ ?_
  · intro s
    apply coprod.hom_ext <;> simp [desc, left]
  · intro s
    apply coprod.hom_ext
    · simpa [desc, right] using s.condition
    · simp [desc, right]
  · intro s m hm hn
    have h₁ := congrArg (fun z ↦ (coprod.inl : B ⟶ B ⨿ E) ≫ z) hm
    have h₂ := congrArg (fun z ↦ (coprod.inr : E ⟶ B ⨿ E) ≫ z) hm
    have h₃ := congrArg (fun z ↦ (coprod.inr : E ⟶ B ⨿ E) ≫ z) hn
    apply coprod.hom_ext
    · simpa [desc, left, Category.assoc] using h₁
    · apply coprod.hom_ext
      · simpa [desc, left, Category.assoc] using h₂
      · simpa [desc, right, Category.assoc] using h₃

end
end ManuscriptAudit.AffineStageFixedCoproductSquare

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineStageFixedCoproductSquare.isPushout
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
