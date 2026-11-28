import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleNestedSectionComparison
import PrimalitySheafVerification.ManuscriptAudit.NestedAffineEtaleRestriction

/-! Literal restriction of a section on nested ambient étale objects also
computes the restriction after passing to the actual affine bases. -/

namespace ManuscriptAudit.NestedAffineEtaleSectionNaturality

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open AffineEtaleCechRestriction NestedAffineEtaleRestriction OpenEtaleExtension
open NestedOpenEtaleSectionNaturality OpenEtaleHOneByRepresentatives
open EtaleTwoOpenHOne AffineEtaleNestedSectionComparison

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]
variable {Y : Scheme.{0}} (j : X A ⟶ Y) [IsOpenImmersion j]
variable (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{0})

private abbrev E (R : Type) [CommRing R] := Scheme.AffineEtale.sheafEquiv (X R) AddCommGrpCat.{0}
private abbrev H := (restriction j AddCommGrpCat.{0}).obj F
private abbrev counitRestriction :=
  (restriction (i A S) AddCommGrpCat.{0}).map ((E A).counitIso.hom.app (H A j F))
private abbrev compRestriction := (restrictionCompIso (i A S) j).hom.app F

private theorem nestedRestrictionIso_app :
    (nestedRestrictionIso (i A S) j).hom.app F =
      (E S).inverse.map (counitRestriction A S j F ≫ compRestriction A S j F) := by
  simp [nestedRestrictionIso, Functor.map_comp, counitRestriction, compRestriction]

/-- The affine section comparison intertwines actual restriction to the
nested open with actual ambient restriction on the étale site. -/
theorem affineSectionEquiv_nested (x : F.obj.obj (op (Scheme.Etale.mk j))) :
    ((nestedRestrictionIso (i A S) j).hom.app F).hom.app (op (baseObject S))
      ((restrictSection (i A S) ((restrictToAffine j).obj F) (baseMap A S)).hom
        (affineSectionEquiv j F x)) =
    affineSectionEquiv (i A S ≫ j) F (F.obj.map (nestedObjectArrow (i A S) j).op x) := by
  rw [nestedRestrictionIso_app]
  let t := op (identityObject (X S))
  change (compRestriction A S j F).hom.app t
    ((counitRestriction A S j F).hom.app t
      ((restrictSection (i A S) ((E A).inverse.obj (H A j F)) (baseMap A S)).hom
        (sectionEquiv j F x))) = _
  rw [affineSection_counit A S (H A j F)]
  exact sectionEquiv_nested (i A S) j F x

end

end ManuscriptAudit.NestedAffineEtaleSectionNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NestedAffineEtaleSectionNaturality.affineSectionEquiv_nested
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
