import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitComparison

/-! Postcomposition along an open immersion on the actual affine basis of
the small étale site, with the square relating the full and affine sites. -/

namespace ManuscriptAudit.AffineEtaleOpenRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenEtaleExtension KummerUnitsSheaf

noncomputable section

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Compose an affine étale object over an open with its open immersion. -/
def affinePostcompose : U.AffineEtale ⥤ X.AffineEtale where
  obj V := by
    letI : Etale V.hom := V.prop
    exact Scheme.AffineEtale.mk (V.hom ≫ j)
  map f := MorphismProperty.CostructuredArrow.homMk f.left trivial (by
    change Scheme.Spec.map f.left ≫ _ ≫ j = _ ≫ j
    rw [← Category.assoc, f.w] <;> simp [Functor.fromPUnit])
  map_id _ := by apply MorphismProperty.CostructuredArrow.Hom.ext; rfl
  map_comp _ _ := by apply MorphismProperty.CostructuredArrow.Hom.ext; rfl

/-- Postcomposition commutes with taking the spectrum of each affine object. -/
def postcomposeSpecIso :
    affinePostcompose j ⋙ Scheme.AffineEtale.Spec X ≅
      Scheme.AffineEtale.Spec U ⋙ etalePostcompose j :=
  NatIso.ofComponents
    (fun V => MorphismProperty.Over.isoMk (Iso.refl (Spec V.left.unop)) (by
      change 𝟙 _ ≫ (V.hom ≫ j) = V.hom ≫ j
      exact Category.id_comp _))
    (by
      intro V T f
      apply (Scheme.Etale.forget X).map_injective
      apply CostructuredArrow.hom_ext
      change Scheme.Spec.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ Scheme.Spec.map f.left
      rw [Category.comp_id, Category.id_comp])


private abbrev C := AddCommGrpCat.{u}
private abbrev basisEquiv (Y : Scheme.{u}) := Scheme.AffineEtale.sheafEquiv Y C.{u}

/-- Restriction transported to the native affine bases of the étale sites. -/
def affineRestriction :
    Sheaf (Scheme.AffineEtale.topology X) C.{u} ⥤
      Sheaf (Scheme.AffineEtale.topology U) C.{u} :=
  (basisEquiv X).functor ⋙ restriction j C.{u} ⋙ (basisEquiv U).inverse

/-- Extension by zero is an exact left adjoint, so the actual affine-basis
restriction preserves injective sheaves. -/
theorem affineRestriction_preservesInjectiveObjects :
    (affineRestriction j).PreservesInjectiveObjects := by
  let E := extensionByZero j C.{u}
  letI : PreservesFiniteLimits E := (extensionByZero_exact j).1
  letI : (restriction j C.{u}).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (abelianExtensionByZeroAdjunction j)
  unfold affineRestriction
  infer_instance

/-- The genuine affine restriction is exact. -/
theorem affineRestriction_exact :
    PreservesFiniteLimits (affineRestriction j) ∧
      PreservesFiniteColimits (affineRestriction j) := by
  letI : PreservesFiniteLimits (restriction j C.{u}) := (restriction_exact j).1
  letI : PreservesFiniteColimits (restriction j C.{u}) := (restriction_exact j).2
  unfold affineRestriction
  exact ⟨inferInstance, inferInstance⟩

private def basisUnitIso (Y : Scheme.{0}) :
    (basisEquiv Y).inverse.obj (fullCoordinateUnitSheaf Y) ≅ coordinateUnitSheaf Y := by
  apply (fullyFaithfulSheafToPresheaf (Scheme.AffineEtale.topology Y) AddCommGrpCat.{0}).preimageIso
  change (Scheme.AffineEtale.Spec Y).op ⋙ fullCoordinateUnits Y ≅
    KummerUnitsPresheaf.units Y
  exact affineRestrictionUnitsIso Y

/-- Genuine affine coordinate-unit sheaves compare under this restriction. -/
def affineRestrictionUnitIso {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] :
    (affineRestriction j).obj (coordinateUnitSheaf X) ≅ coordinateUnitSheaf U := by
  let E := basisEquiv X
  let i : E.functor.obj (coordinateUnitSheaf X) ≅ fullCoordinateUnitSheaf X :=
    E.functor.mapIso (basisUnitIso X).symm ≪≫ E.counitIso.app _
  exact (basisEquiv U).inverse.mapIso ((restriction j AddCommGrpCat.{0}).mapIso i ≪≫
    OpenEtaleUnitComparison.restrictionIso j) ≪≫ basisUnitIso U

end

end ManuscriptAudit.AffineEtaleOpenRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleOpenRestriction.affinePostcompose,
      ``ManuscriptAudit.AffineEtaleOpenRestriction.postcomposeSpecIso,
      ``ManuscriptAudit.AffineEtaleOpenRestriction.affineRestriction_preservesInjectiveObjects,
      ``ManuscriptAudit.AffineEtaleOpenRestriction.affineRestriction_exact,
      ``ManuscriptAudit.AffineEtaleOpenRestriction.affineRestrictionUnitIso] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
