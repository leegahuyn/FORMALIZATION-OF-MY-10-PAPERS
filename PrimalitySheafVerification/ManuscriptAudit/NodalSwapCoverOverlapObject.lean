import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverOverlap

/-! The proper nodal chart intersection is an actual affine object of
the affine étale site of the Z-chart. On this object the nodal trace
has an actual section, given by the first normalization sheet. -/

namespace ManuscriptAudit.NodalSwapCoverOverlapObject

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (affineNode affineOpen)
open NodalProperYChart (chartOpen)
open NodalChartIntersection (intersectionIsoParameter intersectionIsoParameter_inv_fst)
open NodalConductor (coordinates)
open NodalSwapCover (Cover)
open NodalSwapCoverOverlap (overlapSection)
open NodalYChartOverlapPlane (toAffineNode zParameter)
open NodalSwapCoverAffineTrace (affineTrace)
open NodalSwapCoverLocalTrace (affineTrace_surjective_of_section)
open NodalSwapCoverSheafTrace (trace trace_app_surjective_of_affine_trace_surjective)
open AffineEtaleTensorPresentation (objectRing objectAlgebra structureRingHom spec_structureRingHom)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] objectAlgebra

universe u
variable (K : Type u) [Field K]

instance parameterToAffine_isOpenImmersion : IsOpenImmersion (toAffineNode K) := by
  rw [← intersectionIsoParameter_inv_fst]
  infer_instance

/-- The normalized intersection, represented as an affine étale object over Z. -/
def overlapAffineObject : (affineNode K).AffineEtale :=
  Scheme.AffineEtale.mk (toAffineNode K)

/-- Its actual small-site object is the overlap with the second chart. -/
def overlapAffineObjectIso :
    Scheme.Etale.mk (pullback.fst (affineOpen K) (chartOpen K)) ≅
      ((Scheme.AffineEtale.Spec (affineNode K)).obj (overlapAffineObject K)) :=
  MorphismProperty.Over.isoMk (intersectionIsoParameter K) (by
    change (intersectionIsoParameter K).hom ≫ toAffineNode K =
      pullback.fst (affineOpen K) (chartOpen K)
    rw [← intersectionIsoParameter_inv_fst, ← Category.assoc, Iso.hom_inv_id, Category.id_comp])

private theorem overlapObject_structureMap :
    structureRingHom (coordinates K) (overlapAffineObject K) =
      CommRingCat.ofHom (zParameter K).toRingHom := by
  apply Spec.map_injective
  rw [spec_structureRingHom] <;> rfl

/-- The actual affine étale overlap object admits one sheet of the nodal cover. -/
def overlapObjectSection :
    Cover K →ₐ[coordinates K] objectRing (coordinates K) (overlapAffineObject K) where
  toRingHom := (overlapSection K).toRingHom
  commutes' a := by
    have h := (overlapSection K).commutes a
    change (overlapSection K).toRingHom (algebraMap (coordinates K) (Cover K) a) =
      (zParameter K).toRingHom a at h
    change _ = (structureRingHom (coordinates K) (overlapAffineObject K)).hom a
    rw [overlapObject_structureMap]
    exact h

variable (M : AddCommGrpCat.{u}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

set_option maxHeartbeats 1700000 in
/-- The actual trace on sections is surjective on the affine overlap object. -/
theorem trace_overlapObject_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective ((trace K M h2).hom.app (Opposite.op (overlapAffineObject K))) := by
  apply trace_app_surjective_of_affine_trace_surjective
  exact affineTrace_surjective_of_section K _ M h2 (overlapObjectSection K)

end
end ManuscriptAudit.NodalSwapCoverOverlapObject

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSwapCoverOverlapObject.overlapAffineObjectIso,
      ``ManuscriptAudit.NodalSwapCoverOverlapObject.overlapObjectSection,
      ``ManuscriptAudit.NodalSwapCoverOverlapObject.trace_overlapObject_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
