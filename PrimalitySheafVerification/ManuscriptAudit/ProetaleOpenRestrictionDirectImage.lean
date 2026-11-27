import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedImageOpenSupport

/-! Native direct image along a map landing in an open restricts to its direct
image on the open. For a closed image, extension by zero recovers it. -/

namespace ManuscriptAudit.ProetaleOpenRestrictionDirectImage

open AlgebraicGeometry CategoryTheory
open OpenProetaleExtension
open ProetaleBaseChange (baseChange directImage)
open ProetaleContinuousDirectImageMaps (functionsOver functions)
open ProetaleClosedImageOpenSupport (closedImageExtensionIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (k : Z ⟶ Y)

private abbrev A := AddCommGrpCat.{1}
private abbrev J (T : Scheme.{0}) := Scheme.ProEt.topology T

/-- Native pullback over the open cancels its fully faithful postcomposition. -/
def siteIso :
    proetalePostcompose j ⋙ baseChange (k ≫ j) ≅ baseChange k := by
  let P := proetalePostcompose j
  let B := baseChange j
  let a : P ⊣ B := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (show WeaklyEtale j from inferInstance) trivial
  letI : P.Full := (postcomposeFullyFaithful j).full
  letI : P.Faithful := (postcomposeFullyFaithful j).faithful
  let c : baseChange (k ≫ j) ≅ B ⋙ baseChange k :=
    MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) k j
  exact isoWhiskerLeft P c ≪≫ (Functor.associator P B (baseChange k)).symm ≪≫
    isoWhiskerRight (asIso a.unit).symm (baseChange k) ≪≫ Functor.leftUnitor _

/-- Restriction of the actual full native direct image to the open. -/
def restrictionDirectImageCompIso :
    directImage (k ≫ j) A ⋙ restriction j A ≅ directImage k A := by
  letI := postcomposeContinuous j
  exact Functor.sheafPushforwardContinuousComp' (eFG := siteIso j k) (A := A)
    (J := J Y) (K := J X) (L := J Z)

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- Extending the native direct image from the open recovers the composite closed direct image. -/
def extensionDirectImageIso [IsClosedImmersion (k ≫ j)] :
    (extensionByZero j A).obj (functionsOver M k) ≅ functionsOver M (k ≫ j) :=
  ((extensionByZero j A).mapIso
    ((restrictionDirectImageCompIso j k).app (functions M Z)).symm) ≪≫
  closedImageExtensionIso j (k ≫ j) M (by
    rintro _ ⟨z, rfl⟩
    exact ⟨k z, rfl⟩)

end
end ManuscriptAudit.ProetaleOpenRestrictionDirectImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenRestrictionDirectImage.siteIso,
      ``ManuscriptAudit.ProetaleOpenRestrictionDirectImage.restrictionDirectImageCompIso,
      ``ManuscriptAudit.ProetaleOpenRestrictionDirectImage.extensionDirectImageIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
