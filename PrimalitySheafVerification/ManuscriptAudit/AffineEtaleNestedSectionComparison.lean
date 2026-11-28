import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleNestedSectionGeometry
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCechRestriction

/-! Pullback of actual sections from the affine basis compares with the
same open restriction in the entire small étale site. -/

namespace ManuscriptAudit.AffineEtaleNestedSectionComparison

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open AffineEtaleRestrictionEvaluation AffineEtaleCechRestriction
open OpenEtaleExtension EtaleTwoOpenHOne OpenEtaleHOneByRepresentatives
open AffineEtaleNestedSectionGeometry

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem inverse_map_counit {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) (Y : D) :
    e.inverse.map (e.counitIso.hom.app Y) = e.unitIso.inv.app (e.inverse.obj Y) := by
  apply (cancel_epi (e.unitIso.hom.app (e.inverse.obj Y))).mp
  rw [e.unit_inverse_comp, e.unitIso_hom_inv_id_app]

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]

private abbrev E (R : Type) [CommRing R] := Scheme.AffineEtale.sheafEquiv (X R) AddCommGrpCat.{0}
private abbrev T (R : Type) [CommRing R] := identityObject (X R)
private abbrev R := restriction (i A S) AddCommGrpCat.{0}

variable (H : Sheaf (X A).smallEtaleTopology AddCommGrpCat.{0})

private abbrev Haff := (E A).inverse.obj H
private abbrev Hfull := (E A).functor.obj (Haff A H)
private abbrev counit := (E A).counitIso.hom.app H
private abbrev a := ((postcomposeSpecIso (i A S)).hom.app (baseObject S))

private theorem affineComparison_hom :
    (restrictionPresheafIso (i A S) (Haff A H)).hom.app (op (baseObject S)) =
      ((R A S).map (counit A H)).hom.app (op (T S)) ≫ H.obj.map (a A S).op := by
  let P := (Scheme.AffineEtale.Spec (X A)).obj ((affinePostcompose (i A S)).obj (baseObject S))
  let u := (E A).unitIso.inv.app (Haff A H)
  have hu : u = (E A).inverse.map (counit A H) := (inverse_map_counit (E A) H).symm
  change (Hfull A H).obj.map (a A S).op ≫
      u.hom.app (op ((affinePostcompose (i A S)).obj (baseObject S))) =
    (counit A H).hom.app (op ((etalePostcompose (i A S)).obj (T S))) ≫
      H.obj.map (a A S).op
  rw [hu]
  change (Hfull A H).obj.map (a A S).op ≫ (counit A H).hom.app (op P) = _
  exact (counit A H).hom.naturality (a A S).op

/-- The affine section pullback, followed by the actual equivalence counit,
is restriction along the literal open arrow of the full small étale site. -/
theorem affineSection_counit (x : H.obj.obj (op (T A))) :
    ((R A S).map (counit A H)).hom.app (op (T S))
      ((restrictSection (i A S) (Haff A H) (baseMap A S)).hom x) =
    sectionEquiv (i A S) H (H.obj.map (openArrow (i A S)).op x) := by
  let e := (restrictionPresheafIso (i A S) (Haff A H)).app (op (baseObject S))
  let r := (Scheme.AffineEtale.Spec (X A)).map (baseMap A S)
  have hx : e.hom ((restrictSection (i A S) (Haff A H) (baseMap A S)).hom x) =
      H.obj.map r.op x := by
    change e.hom (e.inv (H.obj.map r.op x)) = _
    exact e.inv_hom_id_apply _
  have hE : e.hom =
      ((R A S).map (counit A H)).hom.app (op (T S)) ≫ H.obj.map (a A S).op :=
    affineComparison_hom A S H
  rw [hE, ConcreteCategory.comp_apply] at hx
  apply (H.obj.mapIso ((postcomposeSpecIso (i A S)).app (baseObject S)).op).addCommGroupIsoToAddEquiv.injective
  exact hx.trans (terminalSectionsSpec A S H x).symm

end

end ManuscriptAudit.AffineEtaleNestedSectionComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleNestedSectionComparison.affineSection_counit
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
