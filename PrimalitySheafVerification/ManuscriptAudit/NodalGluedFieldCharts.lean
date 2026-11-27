import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalGluedFieldOverlapCoordinates
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection

/-! The actual field-model identifications commute with both chart projections. -/

namespace ManuscriptAudit.NodalGluedFieldCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralChartTransition NodalIntegralGluing
open NodalYChartOverlap (parameterRing t tInv denominatorInv denominator_mul_inv)
open NodalYChartOverlapPlane (parameterScheme zParameter toAffineNode toNodeYChart)
open NodalProjectiveClosure (affineNode)
open NodalYChartImmersion (nodeYChart yCoordinateRing xCoeff zCoeff)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 190000
set_option synthInstance.maxHeartbeats 16000

universe u
variable (K : Type u) [Field K]

private theorem yInZ_parameter :
    (zOverlapEquiv K).toAlgHom.comp (yInZ K) =
      (NodalYChartOverlap.yToParameter K).comp (yChartEquiv K).toAlgHom := by
  apply chart_hom_ext K
  · change zOverlapEquiv K (yInZ K (xY K)) =
      NodalYChartOverlap.yToParameter K (yChartEquiv K (xY K))
    rw [yInZ_x, map_mul, zOverlapEquiv_x, zOverlapEquiv_inv, yChartEquiv_x,
      NodalYChartOverlap.yToParameter_x] <;> rfl
  · change zOverlapEquiv K (yInZ K (zY K)) =
      NodalYChartOverlap.yToParameter K (yChartEquiv K (zY K))
    rw [yInZ_z, zOverlapEquiv_inv, yChartEquiv_z, NodalYChartOverlap.yToParameter_z]

def overlapSchemeIso : parameterScheme K ≅ overlapScheme K :=
  Scheme.Spec.mapIso (zOverlapEquiv K).toCommRingCatIso.op

@[reassoc]
theorem overlapSchemeIso_toZ :
    (overlapSchemeIso K).hom ≫ overlapToZ K ≫ (zSchemeIso K).hom = toAffineNode K := by
  change Spec.map (CommRingCat.ofHom (zOverlapEquiv K).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (zChart K) (zOverlap K))) ≫
    Spec.map (CommRingCat.ofHom (zChartEquiv K).symm.toRingHom) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change zOverlapEquiv K
    (algebraMap (zChart K) (zOverlap K) ((zChartEquiv K).symm a)) = zParameter K a
  rw [zOverlapEquiv_algebraMap, AlgEquiv.apply_symm_apply]

@[reassoc]
theorem overlapSchemeIso_toY :
    (overlapSchemeIso K).hom ≫ overlapToY K ≫ (ySchemeIso K).hom = toNodeYChart K := by
  change Spec.map (CommRingCat.ofHom (zOverlapEquiv K).toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (transition K).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (yChart K) (yOverlap K)))) ≫
    Spec.map (CommRingCat.ofHom (yChartEquiv K).symm.toRingHom) = _
  simp only [Category.assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change zOverlapEquiv K (yToZ K
    (algebraMap (yChart K) (yOverlap K) ((yChartEquiv K).symm a))) =
      NodalYChartOverlap.yToParameter K a
  rw [yToZ_algebraMap]
  have h := DFunLike.congr_fun (yInZ_parameter K) ((yChartEquiv K).symm a)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply] using h

end
end ManuscriptAudit.NodalGluedFieldCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalGluedFieldCharts.overlapSchemeIso_toZ,
      ``ManuscriptAudit.NodalGluedFieldCharts.overlapSchemeIso_toY] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
