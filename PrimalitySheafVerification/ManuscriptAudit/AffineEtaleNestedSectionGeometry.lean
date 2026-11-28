import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleOpenBaseChange
import PrimalitySheafVerification.ManuscriptAudit.NestedOpenEtaleSectionNaturality

/-! The actual terminal affine-basis restriction arrow and the open
restriction arrow become the same map of small étale objects. -/

namespace ManuscriptAudit.AffineEtaleNestedSectionGeometry

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open OpenEtaleExtension EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]

/-- Postcomposition of the affine terminal object becomes the literal open
object under the spectrum functor. -/
def openObjectIso :
    (etalePostcompose (i A S)).obj (identityObject (X S)) ≅
      Scheme.Etale.mk (i A S) :=
  MorphismProperty.Over.isoMk (Iso.refl (X S)) (by rfl)

/-- The actual affine restriction arrow becomes the scheme open arrow. -/
theorem terminalArrowSpec :
    ((postcomposeSpecIso (i A S)).hom.app (baseObject S)) ≫
      (openObjectIso A S).hom ≫ openArrow (i A S) =
    (Scheme.AffineEtale.Spec (X A)).map (baseMap A S) := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 (X S) ≫ 𝟙 (X S) ≫ i A S = i A S
  simp

/-- Evaluating the actual section map carries out literal restriction
along the open arrow after either affine or full postcomposition. -/
theorem terminalSectionsSpec (F : Sheaf (X A).smallEtaleTopology AddCommGrpCat)
    (x : F.obj.obj (op (identityObject (X A)))) :
    F.obj.map (((postcomposeSpecIso (i A S)).hom.app (baseObject S)).op)
      (OpenEtaleHOneByRepresentatives.sectionEquiv (i A S) F
        (F.obj.map (openArrow (i A S)).op x)) =
    F.obj.map ((Scheme.AffineEtale.Spec (X A)).map (baseMap A S)).op x := by
  let a := ((postcomposeSpecIso (i A S)).hom.app (baseObject S))
  let b := (openObjectIso A S).hom
  let c := openArrow (i A S)
  change F.obj.map a.op (F.obj.map b.op (F.obj.map c.op x)) = _
  have h : F.obj.map a.op (F.obj.map b.op (F.obj.map c.op x)) =
      F.obj.map (a ≫ b ≫ c).op x := by
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  rw [h, terminalArrowSpec A S]

end

end ManuscriptAudit.AffineEtaleNestedSectionGeometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleNestedSectionGeometry.terminalArrowSpec,
      ``ManuscriptAudit.AffineEtaleNestedSectionGeometry.terminalSectionsSpec] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
