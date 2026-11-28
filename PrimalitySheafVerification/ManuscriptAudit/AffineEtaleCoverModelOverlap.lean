import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCoverModelIso

/-! Transport of the actual two overlap arrows along the affine
cover-model isomorphism, keeping both matching relations. -/

namespace ManuscriptAudit.AffineEtaleCoverModelOverlap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private theorem exists_overlap_map {C : Type*} [Category* C]
    {B₀ B F₀ F O₀ O : C} {f₀ : B₀ ⟶ F₀} {f : B ⟶ F}
    {p₀ q₀ : F₀ ⟶ O₀} {p q : F ⟶ O}
    (j : B₀ ≅ B) (e : F₀ ≅ F)
    (h : f₀ ≫ e.hom = j.hom ≫ f) (h₀ : f₀ ≫ p₀ = f₀ ≫ q₀)
    (hP : IsPushout f f p q) :
    ∃ w : O ⟶ O₀, p ≫ w = e.inv ≫ p₀ ∧ q ≫ w = e.inv ≫ q₀ := by
  have hf : f ≫ e.inv = j.inv ≫ f₀ := by
    rw [← cancel_mono e.hom, Category.assoc, e.inv_hom_id, Category.comp_id,
      Category.assoc, h, j.inv_hom_id_assoc]
  have hw : f ≫ (e.inv ≫ p₀) = f ≫ (e.inv ≫ q₀) := by
    rw [← Category.assoc, ← Category.assoc, hf, Category.assoc, Category.assoc, h₀]
  exact ⟨hP.desc _ _ hw, hP.inl_desc _ _ _, hP.inr_desc _ _ _⟩

variable {A B F : Type u} [CommRing A] [CommRing B] [CommRing F]
  [Algebra A B] [Algebra B F] [Algebra A F] [IsScalarTower A B F]

private abbrev U (W : Type u) [CommRing W] [Algebra A W] := CommRingCat.mkUnder (CommRingCat.of A) W

abbrev inl : F →ₐ[A] F ⊗[B] F := (Algebra.TensorProduct.includeLeft : F →ₐ[B] _).restrictScalars A
abbrev inr : F →ₐ[A] F ⊗[B] F := (Algebra.TensorProduct.includeRight : F →ₐ[B] _).restrictScalars A

private abbrev f := (IsScalarTower.toAlgHom A B F).toUnder

/-- The ring of the actual relative self-intersection is the
self-pushout, also retaining its map from the original base. -/
theorem tensor_isPushout :
    IsPushout (f (A := A) (B := B) (F := F)) (f (A := A) (B := B) (F := F))
      (inl (A := A) (B := B) (F := F)).toUnder (inr (A := A) (B := B) (F := F)).toUnder := by
  apply IsPushout.of_map_of_faithful (Under.forget (CommRingCat.of A))
  exact CommRingCat.isPushout_tensorProduct B F F

/-- After identifying the cover with its fixed model, the literal
relative tensor witness gives both equations over the model's overlap. -/
theorem exists_tensor_overlap_map
    {B₀ F₀ O₀ : Under (CommRingCat.of A)} {f₀ : B₀ ⟶ F₀} {p₀ q₀ : F₀ ⟶ O₀}
    (j : B₀ ≅ U (A := A) B) (e : F₀ ≅ U (A := A) F)
    (h : f₀ ≫ e.hom = j.hom ≫ f (A := A) (B := B) (F := F))
    (h₀ : f₀ ≫ p₀ = f₀ ≫ q₀) :
    ∃ w : U (A := A) (F ⊗[B] F) ⟶ O₀,
      (inl (A := A) (B := B) (F := F)).toUnder ≫ w = e.inv ≫ p₀ ∧
      (inr (A := A) (B := B) (F := F)).toUnder ≫ w = e.inv ≫ q₀ :=
  exists_overlap_map j e h h₀ tensor_isPushout

end
end ManuscriptAudit.AffineEtaleCoverModelOverlap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleCoverModelOverlap.tensor_isPushout,
      ``ManuscriptAudit.AffineEtaleCoverModelOverlap.exists_tensor_overlap_map] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
