import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageComma
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleKanComparison

/-! At the actual affine chart, the raw affine-étale Kan extension
is the filtered colimit of the genuine affine étale stage sections. -/

namespace ManuscriptAudit.NativeAffineEtaleRawSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage)
open NativeAffineEtaleStageSections (chartArrow etaleObject sectionDiagram sectionCocone)
open NativeAffineEtaleKanComparison (L affineRestriction raw toNative)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}
private abbrev V := op (ProetaleAffineTensor.object A B)

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private abbrev P := ((affineRestriction (X (A := A))).obj I).obj

private abbrev K := L (X (A := A))

private abbrev η := (K (A := A)).lanUnit.app (P I)

private abbrev E := NativeAffineEtaleStageComma.equivalence (A := A) (B := B)

private def indexCocone :=
  (CategoryTheory.Functor.LeftExtension.mk _ (η I)).coconeAt (V (A := A) (B := B))

private def indexIsColimit : IsColimit (indexCocone (B := B) I) :=
  (CategoryTheory.Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (K (A := A)) (P I))
    (V (A := A) (B := B))

private def stageComparison :
    (E (A := A) (B := B)).functor ⋙
      CostructuredArrow.proj (K (A := A)) (V (A := A) (B := B)) ⋙ P I ≅
        sectionDiagram (B := B) I :=
  Functor.isoWhiskerRight
    (NativeAffineEtaleStageComma.etaleDiagramIso (A := A) (B := B)) I.obj

/-- The raw section cocone uses the actual affine étale stages of the chart. -/
def rawSectionCocone : Cocone (sectionDiagram (B := B) I) :=
  (Cocone.precompose (stageComparison (B := B) I).inv).obj
    ((indexCocone (B := B) I).whisker (E (A := A) (B := B)).functor)

set_option maxHeartbeats 3600000 in
/-- Before sheafification, the sections on the actual chart are the
literal filtered colimit of the actual affine étale evaluations. -/
def isColimit_rawSectionCocone : IsColimit (rawSectionCocone (B := B) I) :=
  (IsColimit.precomposeHomEquiv (stageComparison (B := B) I).symm _).symm
    ((indexIsColimit (B := B) I).whiskerEquivalence (E (A := A) (B := B)))

set_option maxHeartbeats 4000000 in
/-- The canonical map of this raw colimit to the actual inverse image
has exactly the adjunction-unit restrictions on all stage sections. -/
theorem raw_toNative_fac (T : Stage A B) :
    (rawSectionCocone (B := B) I).ι.app T ≫
      (toNative (X (A := A)) I).app (V (A := A) (B := B)) =
      (sectionCocone (B := B) I).ι.app T := by
  let Y := X (A := A)
  let R := affineRestriction Y
  let a := EtaleProetaleInverseImage.adjunction Y
  let b := (K (A := A)).lanAdjunction G.{u}
  let d := toNative Y I
  have hb : b.homEquiv (P I) _ d = (R.map (a.unit.app I)).hom :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at hb
  let U := ((E (A := A) (B := B)).functor.obj T).left
  have h := congrArg (fun p ↦ p.app U) hb
  change (η I).app U ≫ d.app ((K (A := A)).obj U) =
    (a.unit.app I).hom.app (op (etaleObject T)) at h
  change (𝟙 _ ≫ ((η I).app U ≫ (raw Y I).map (chartArrow T).op)) ≫
      d.app (V (A := A) (B := B)) =
    (a.unit.app I).hom.app (op (etaleObject T)) ≫
      ((EtaleProetaleInverseImage.inverseImage Y).obj I).obj.map (chartArrow T).op
  rw [Category.id_comp, Category.assoc, d.naturality, ← Category.assoc, h]

end
end ManuscriptAudit.NativeAffineEtaleRawSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineEtaleRawSections.isColimit_rawSectionCocone,
      ``ManuscriptAudit.NativeAffineEtaleRawSections.raw_toNative_fac] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
