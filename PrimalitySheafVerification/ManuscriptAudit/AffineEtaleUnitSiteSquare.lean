import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleConstantRestrictionSquare
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictedUnits
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictionNaturality

/-! The full-site and affine-basis restriction square is compatible
with the two actual coordinate-unit sheaves. -/

namespace ManuscriptAudit.AffineEtaleUnitSiteSquare

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleOpenRestriction AffineEtaleRestrictionEvaluation
open AffineEtaleRestrictionNaturality AffineEtaleRestrictedUnits
open AffineEtaleConstantRestrictionSquare OpenEtaleExtension
open KummerUnitsSheaf KummerUnitsPresheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev B := AddCommGrpCat.{0}
private abbrev G (Y : Scheme.{0}) := fullCoordinateUnitSheaf Y
private abbrev G' (Y : Scheme.{0}) := coordinateUnitSheaf Y
private abbrev E (Y : Scheme.{0}) := Scheme.AffineEtale.sheafEquiv Y B

/-- The literal affine-basis comparison on the coordinate-unit sheaf. -/
def basisUnitsIso (Y : Scheme.{0}) : (E Y).inverse.obj (G Y) ≅ G' Y :=
  (fullyFaithfulSheafToPresheaf (Scheme.AffineEtale.topology Y) B).preimageIso
    (affineRestrictionUnitsIso Y)

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev R := restriction j B
private abbrev u := (OpenEtaleUnitComparison.restrictionIso j).hom

private theorem inverse_map_counit (H : Sheaf X.smallEtaleTopology B) :
    (E X).inverse.map ((E X).counitIso.hom.app H) =
      (E X).unitIso.inv.app ((E X).inverse.obj H) := by
  apply (cancel_epi ((E X).unitIso.hom.app ((E X).inverse.obj H))).mp
  exact ((E X).unit_inverse_comp H).trans ((E X).unitIso_hom_inv_id_app ((E X).inverse.obj H)).symm

private theorem comparison_hom (H : Sheaf X.smallEtaleTopology B) (D : U.AffineEtale) :
    (restrictionPresheafIso j ((E X).inverse.obj H)).hom.app (op D) =
      ((R j).map ((E X).counitIso.hom.app H)).hom.app (op ((Scheme.AffineEtale.Spec U).obj D)) ≫
        H.obj.map (((postcomposeSpecIso j).hom.app D)).op := by
  let a := ((postcomposeSpecIso j).hom.app D).op
  let c := (E X).counitIso.hom.app H
  let I := (E X).inverse.obj H
  change ((E X).functor.obj I).obj.map a ≫
      ((E X).unitIso.inv.app I).hom.app (op ((affinePostcompose j).obj D)) = _
  rw [← inverse_map_counit H]
  change ((E X).functor.obj I).obj.map a ≫ c.hom.app _ = c.hom.app _ ≫ H.obj.map a
  exact c.hom.naturality a

private theorem unit_component (D : U.AffineEtale) :
    ((affineRestriction j).map (basisUnitsIso X).hom).hom.app (op D) ≫
        (restrictionUnitsIso j).hom.hom.app (op D) =
      ((R j).map ((E X).counitIso.hom.app (G X))).hom.app (op ((Scheme.AffineEtale.Spec U).obj D)) ≫
        (u j).hom.app (op ((Scheme.AffineEtale.Spec U).obj D)) ≫ (basisUnitsIso U).hom.hom.app (op D) := by
  let a := ((postcomposeSpecIso j).hom.app D).op
  have hu : (restrictionUnitsIso j).hom.hom.app (op D) =
      (restrictionPresheafIso j (G' X)).hom.app (op D) := by
    change (restrictionPresheafIso j (G' X)).hom.app (op D) ≫ 𝟙 _ = _
    rw [Category.comp_id]
  rw [hu, restrictionPresheafIso_natural j (basisUnitsIso X).hom D, comparison_hom]
  have hₐ : (G X).obj.map a = 𝟙 _ := by
    change (Scheme.Γ ⋙ ringUnits).map (𝟙 ((Scheme.AffineEtale.Spec U).obj D).left).op = _
    rw [op_id, Functor.map_id]
  rw [hₐ, Category.comp_id]
  change _ ≫ (basisUnitsIso X).hom.hom.app (op ((affinePostcompose j).obj D)) =
    _ ≫ 𝟙 _ ≫ (basisUnitsIso U).hom.hom.app (op D)
  rw [Category.id_comp] <;> rfl

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
private abbrev SpecOf (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]

/-- The actual unit coefficients on either genuine small site intertwine
the respective open restriction morphisms. -/
theorem unit_square :
    (affineRestriction (i A S)).map (basisUnitsIso (SpecOf A)).hom ≫ (restrictionUnitsIso (i A S)).hom =
      (siteSquare A S).hom.app (G (SpecOf A)) ≫
        (E (SpecOf S)).inverse.map (u (i A S)) ≫ (basisUnitsIso (SpecOf S)).hom := by
  apply (sheafToPresheaf (Scheme.AffineEtale.topology (SpecOf S)) B).map_injective
  apply NatTrans.ext
  funext D
  exact unit_component (i A S) D.unop

end

end ManuscriptAudit.AffineEtaleUnitSiteSquare

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleUnitSiteSquare.unit_square
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
