import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageCategory
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! The genuine affine étale stage evaluations of a sheaf have a
canonical cocone in the sections of its actual native inverse image. -/

namespace ManuscriptAudit.NativeAffineEtaleStageSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap specMap)
open AffineEtaleStageCategory (Stage hom)
open EtaleProetaleSiteInclusion (inclusion)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

private abbrev X := spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

private instance (T : Stage A B) : Etale (structureMap A T.carrier) :=
  (Etale.SpecMap_iff (f := CommRingCat.ofHom (algebraMap A T.carrier))).mpr
    ((RingHom.etale_algebraMap).mpr inferInstance)

/-- The genuine small étale object corresponding to a stage. -/
abbrev etaleObject (T : Stage A B) : (X (A := A)).Etale :=
  Scheme.Etale.mk (structureMap A T.carrier)

abbrev etaleMap {T U : Stage A B} (f : T ⟶ U) : etaleObject U ⟶ etaleObject T :=
  MorphismProperty.Over.homMk (specMap A (hom f))
    (ProetaleAffineTensor.specMap_structureMap A (hom f))

/-- The geometric stage diagram is contravariant in the actual ring stages. -/
def etaleDiagram : Stage A B ⥤ (X (A := A)).Etaleᵒᵖ where
  obj T := op (etaleObject T)
  map f := (etaleMap f).op
  map_id T := by
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (𝟙 (CommRingCat.of T.carrier)) = 𝟙 (spectrum T.carrier)
    exact Spec.map_id _
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom ((hom g).comp (hom f)).toRingHom) =
      specMap A (hom g) ≫ specMap A (hom f)
    rw [← Spec.map_comp] <;> rfl

variable [WeaklyEtale (structureMap A B)]

private abbrev chart := ProetaleAffineTensor.object A B

/-- The actual site arrow from the chart to a stage viewed pro-étale. -/
abbrev chartArrow (T : Stage A B) :
    chart (A := A) (B := B) ⟶ (inclusion (X (A := A))).obj (etaleObject T) :=
  MorphismProperty.Over.homMk (specMap A T.toChart)
    (ProetaleAffineTensor.specMap_structureMap A T.toChart)

theorem chartArrow_natural {T U : Stage A B} (f : T ⟶ U) :
    chartArrow U ≫ (inclusion (X (A := A))).map (etaleMap f) = chartArrow T := by
  apply MorphismProperty.Over.Hom.ext
  change specMap A U.toChart ≫ specMap A (hom f) = specMap A T.toChart
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom f.property)

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

/-- Evaluations are on the actual small étale site objects coming
from the genuine affine stages. -/
abbrev sectionDiagram : Stage A B ⥤ G.{u} := etaleDiagram ⋙ I.obj

set_option maxHeartbeats 2900000 in
/-- The maps to the chart are the unit of the actual site adjunction
followed by actual restriction along the chart-to-stage morphisms. -/
def sectionCocone : Cocone (sectionDiagram (B := B) I) := by
  let X₀ := X (A := A)
  let F := (EtaleProetaleInverseImage.inverseImage X₀).obj I
  let η := ((EtaleProetaleInverseImage.adjunction X₀).unit.app I).hom
  let L := inclusion X₀
  refine
    { pt := F.obj.obj (op (chart (A := A) (B := B)))
      ι :=
        { app := fun T ↦ η.app (op (etaleObject T)) ≫ F.obj.map (chartArrow T).op
          naturality := ?_ } }
  intro T U f
  change I.obj.map (etaleMap f).op ≫
      (η.app (op (etaleObject U)) ≫ F.obj.map (chartArrow U).op) =
    (η.app (op (etaleObject T)) ≫ F.obj.map (chartArrow T).op) ≫ 𝟙 _
  rw [Category.comp_id, ← Category.assoc, η.naturality, Category.assoc]
  change η.app (op (etaleObject T)) ≫
      (F.obj.map (L.map (etaleMap f)).op ≫ F.obj.map (chartArrow U).op) =
    η.app (op (etaleObject T)) ≫ F.obj.map (chartArrow T).op
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, chartArrow_natural]

end
end ManuscriptAudit.NativeAffineEtaleStageSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineEtaleStageSections.chartArrow_natural,
      ``ManuscriptAudit.NativeAffineEtaleStageSections.sectionCocone] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
