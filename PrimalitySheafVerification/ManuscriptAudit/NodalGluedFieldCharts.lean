import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralGluing
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection

/-! Over a field, the two charts and the overlap in the integral gluing
diagram are the same actual schemes as the charts of the existing
projective node. -/

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
set_option maxHeartbeats 700000

universe u
variable (K : Type u) [Field K]

def zChartEquiv : zChart K ≃ₐ[K] NodalConductor.coordinates K :=
  NodalAffinePresentation.coordinateEquiv K

private theorem zChartEquiv_x :
    zChartEquiv K (xZ K) = NodalAffinePresentation.nodeX K :=
  (NodalAffinePresentation.parameter_base K Polynomial.X).trans (Polynomial.aeval_X _)

private theorem zChartEquiv_y :
    zChartEquiv K (yZ K) = NodalAwayNormalization.nodeY K :=
  NodalAffinePresentation.parameter_root K

private def rootCongr {p q : Polynomial (Polynomial K)} (h : p = q) :
    AdjoinRoot p ≃ₐ[K] AdjoinRoot q := by
  subst q
  exact .refl

private theorem rootCongr_of {p q : Polynomial (Polynomial K)} (h : p = q)
    (a : Polynomial K) : rootCongr K h (AdjoinRoot.of p a) = AdjoinRoot.of q a := by
  subst q
  rfl

private theorem rootCongr_root {p q : Polynomial (Polynomial K)} (h : p = q) :
    rootCongr K h (AdjoinRoot.root p) = AdjoinRoot.root q := by
  subst q
  rfl

def yChartEquiv : yChart K ≃ₐ[K] yCoordinateRing K :=
  rootCongr K (NodalYChartImmersion.yEquation_printed K).symm

private theorem yChartEquiv_x : yChartEquiv K (xY K) = xCoeff K :=
  rootCongr_of K _ Polynomial.X

private theorem yChartEquiv_z : yChartEquiv K (zY K) = zCoeff K :=
  rootCongr_root K _

private def zOverlapToCoordinates :
    zOverlap K ≃ₐ[K] Localization.Away (NodalAwayNormalization.nodeY K) :=
  IsLocalization.algEquivOfAlgEquiv _ _ (zChartEquiv K) (by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (zChartEquiv_y K))

/-- The overlap of the two glued charts is the actual normalized parameter chart. -/
def zOverlapEquiv : zOverlap K ≃ₐ[K] parameterRing K :=
  (zOverlapToCoordinates K).trans (NodalAwayNormalization.overlapNormalizationEquiv K)

private theorem zOverlapEquiv_algebraMap (a : zChart K) :
    zOverlapEquiv K (algebraMap (zChart K) (zOverlap K) a) =
      zParameter K (zChartEquiv K a) := by
  unfold zOverlapEquiv
  rw [AlgEquiv.trans_apply]
  have h := IsLocalization.algEquivOfAlgEquiv_eq
    (h := zChartEquiv K) (S := zOverlap K)
    (Q := Localization.Away (NodalAwayNormalization.nodeY K))
    (show Submonoid.map (zChartEquiv K) (Submonoid.powers (yZ K)) =
      Submonoid.powers (NodalAwayNormalization.nodeY K) from by
        rw [Submonoid.map_powers]
        exact congrArg Submonoid.powers (zChartEquiv_y K)) a
  change zOverlapToCoordinates K
    (algebraMap (zChart K) (zOverlap K) a) = _ at h
  rw [h]
  change Localization.awayMap (NodalConductor.coordinates K).val.toRingHom
    (NodalAwayNormalization.nodeY K)
    (algebraMap _ _ (zChartEquiv K a)) = _
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq] <;> rfl

private theorem zOverlapEquiv_x :
    zOverlapEquiv K (xZO K) = t K ^ 2 - 1 := by
  unfold xZO
  rw [zOverlapEquiv_algebraMap, zChartEquiv_x]
  change algebraMap (Polynomial K) (parameterRing K) (NodalConductor.x K) = _
  rw [NodalConductor.x, map_sub, map_pow, map_one] <;> rfl

private theorem zOverlapEquiv_y :
    zOverlapEquiv K (yZO K) = t K * (t K ^ 2 - 1) := by
  unfold yZO
  rw [zOverlapEquiv_algebraMap, zChartEquiv_y]
  exact NodalYChartOverlap.denominator_image K

private theorem zOverlapEquiv_inv :
    zOverlapEquiv K (yZOinv K) = denominatorInv K := by
  have h := congrArg (zOverlapEquiv K) (IsLocalization.Away.mul_invSelf
    (S := zOverlap K) (yZ K))
  change zOverlapEquiv K (yZO K * yZOinv K) = zOverlapEquiv K 1 at h
  rw [map_mul, map_one, zOverlapEquiv_y] at h
  calc
    _ = ((denominatorInv K) * (t K * (t K ^ 2 - 1))) *
        zOverlapEquiv K (yZOinv K) := by
          rw [mul_comm (denominatorInv K), denominator_mul_inv, one_mul]
    _ = _ := by rw [mul_assoc, h, mul_one]

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

def zSchemeIso : zScheme K ≅ affineNode K :=
  Scheme.Spec.mapIso (zChartEquiv K).symm.toCommRingCatIso.op

def ySchemeIso : yScheme K ≅ nodeYChart K :=
  Scheme.Spec.mapIso (yChartEquiv K).symm.toCommRingCatIso.op

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
  for name in [``ManuscriptAudit.NodalGluedFieldCharts.zChartEquiv,
      ``ManuscriptAudit.NodalGluedFieldCharts.yChartEquiv,
      ``ManuscriptAudit.NodalGluedFieldCharts.zOverlapEquiv,
      ``ManuscriptAudit.NodalGluedFieldCharts.overlapSchemeIso_toZ,
      ``ManuscriptAudit.NodalGluedFieldCharts.overlapSchemeIso_toY] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
