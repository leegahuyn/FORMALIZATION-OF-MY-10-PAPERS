import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineStageTensorLegs
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRefinementColimit
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFixedCoproductGeometry

/-! The fixed-cover model's tensor description is an isomorphism
over the original affine base, including its actual cover map. -/

namespace ManuscriptAudit.AffineEtaleCoverModelIso

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage)
open AffineEtaleStageRefinementColimit (refinementCocone)
open AffineStageFixedCoproductGeometry (left)
open AffineStageTensorCoproduct (tensorIso tensorCofan)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B F : Type u} [CommRing A] [CommRing B] [CommRing F]
  [Algebra A B] [Algebra B F] [Algebra A F] [IsScalarTower A B F]
  [WeaklyEtale (structureMap A B)]

abbrev original (C : Type u) [CommRing C] [Algebra A C] :=
  CommRingCat.mkUnder (CommRingCat.of A) C

variable (T : Stage A B) (E : Type u) [CommRing E] [Algebra T.carrier E]

abbrev baseArrow := CommRingCat.ofHom (algebraMap A T.carrier)
abbrev baseLimit := (refinementCocone T).pt
abbrev fixedRing := CommRingCat.mkUnder (CommRingCat.of T.carrier) E
abbrev coverLimit := (Under.map (baseArrow T)).obj (baseLimit T ⨿ fixedRing T E)

private theorem base_compat :
    baseArrow T ≫ (baseLimit T).hom = CommRingCat.ofHom (algebraMap A B) := by
  apply CommRingCat.hom_ext
  ext x
  exact T.toChart.commutes x

/-- The original base chart and the limit chart have the same ring. -/
def baseIso : (Under.map (baseArrow T)).obj (baseLimit T) ≅ original (A := A) B :=
  Under.isoMk (Iso.refl _) ((Category.comp_id _).trans (base_compat T))

local instance chartBaseAlgebra : Algebra T.carrier B := T.toChart.toRingHom.toAlgebra

private def ringIso (e : F ≃ₐ[B] B ⊗[T.carrier] E) :
    (coverLimit T E).right ≅ CommRingCat.of F :=
  (Under.forget _).mapIso (tensorIso (R := CommRingCat.of T.carrier) B E).symm ≪≫
    (Under.forget (CommRingCat.of B)).mapIso e.symm.toUnder

private theorem ringIso_cover (e : F ≃ₐ[B] B ⊗[T.carrier] E) :
    (left (baseLimit T) (fixedRing T E)).right ≫ (ringIso T E e).hom =
      CommRingCat.ofHom (algebraMap B F) := by
  let Z := tensorIso (R := CommRingCat.of T.carrier) B E
  have h₀ := AffineStageTensorLegs.inl_tensorIso_hom (R := T.carrier) (S := B) (T := E)
  have h₁ : (coprod.inl : CommRingCat.mkUnder (CommRingCat.of T.carrier) B ⟶ _) ≫ Z.inv =
      (tensorCofan (R := CommRingCat.of T.carrier) B E).inl := by
    rw [← h₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (left (baseLimit T) (fixedRing T E)).right ≫
      (Z.inv.right ≫ e.symm.toUnder.hom.right) = _
  have h₂ : (left (baseLimit T) (fixedRing T E)).right ≫ Z.inv.right =
      (tensorCofan (R := CommRingCat.of T.carrier) B E).inl.right :=
    congrArg (Under.forget (CommRingCat.of T.carrier)).map h₁
  rw [← Category.assoc, h₂]
  exact Under.w e.symm.toUnder.hom

/-- The actual chart of the descended cover is isomorphic over A to
the relative affine étale cover ring F. -/
def coverIso (e : F ≃ₐ[B] B ⊗[T.carrier] E) :
    coverLimit T E ≅ original (A := A) F := by
  refine Under.isoMk (ringIso T E e) ?_
  change (baseArrow T ≫ (baseLimit T ⨿ fixedRing T E).hom) ≫ (ringIso T E e).hom =
      CommRingCat.ofHom (algebraMap A F)
  rw [Category.assoc, ← Under.w (left (baseLimit T) (fixedRing T E)), Category.assoc,
    ringIso_cover T E e, ← Category.assoc, base_compat T]
  apply CommRingCat.hom_ext
  ext x
  exact (IsScalarTower.algebraMap_apply A B F x).symm

/-- The cover's comparison keeps the literal map from the chart. -/
theorem coverIso_leg (e : F ≃ₐ[B] B ⊗[T.carrier] E) :
    (Under.map (baseArrow T)).map (left (baseLimit T) (fixedRing T E)) ≫ (coverIso T E e).hom =
      (baseIso T).hom ≫ (IsScalarTower.toAlgHom A B F).toUnder := by
  apply (Under.forget (CommRingCat.of A)).map_injective
  change (left (baseLimit T) (fixedRing T E)).right ≫ (ringIso T E e).hom =
      (𝟙 (CommRingCat.of B)) ≫ CommRingCat.ofHom (algebraMap B F)
  rw [Category.id_comp]
  exact ringIso_cover T E e

end
end ManuscriptAudit.AffineEtaleCoverModelIso

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleCoverModelIso.coverIso_leg
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
