import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalGluedFieldCoordinates
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartOverlapPlane

/-! Exact overlap normalization for the nodal gluing and field model. -/

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

private theorem overlap_powers :
    Submonoid.map (zChartEquiv K) (Submonoid.powers (yZ K)) =
      Submonoid.powers (NodalAwayNormalization.nodeY K) := by
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (zChartEquiv_y K)

private def zOverlapToCoordinates :
    zOverlap K ≃ₐ[K] Localization.Away (NodalAwayNormalization.nodeY K) :=
  IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers (yZ K))
    (T := Submonoid.powers (NodalAwayNormalization.nodeY K)) _ _
    (zChartEquiv K) (overlap_powers K)

/-- The overlap of the two glued charts is the actual normalized parameter chart. -/
def zOverlapEquiv : zOverlap K ≃ₐ[K] parameterRing K :=
  (zOverlapToCoordinates K).trans (NodalAwayNormalization.overlapNormalizationEquiv K)

theorem zOverlapEquiv_algebraMap (a : zChart K) :
    zOverlapEquiv K (algebraMap (zChart K) (zOverlap K) a) =
      zParameter K (zChartEquiv K a) := by
  unfold zOverlapEquiv
  rw [AlgEquiv.trans_apply]
  have h : zOverlapToCoordinates K (algebraMap (zChart K) (zOverlap K) a) =
      algebraMap (NodalConductor.coordinates K)
        (Localization.Away (NodalAwayNormalization.nodeY K)) (zChartEquiv K a) :=
    IsLocalization.algEquivOfAlgEquiv_eq (h := zChartEquiv K)
      (overlap_powers K) a
  rw [h]
  change Localization.awayMap (NodalConductor.coordinates K).val.toRingHom
    (NodalAwayNormalization.nodeY K)
    (algebraMap _ _ (zChartEquiv K a)) = _
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq] <;> rfl

theorem zOverlapEquiv_x :
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

theorem zOverlapEquiv_inv :
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


end
end ManuscriptAudit.NodalGluedFieldCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalGluedFieldCharts.zOverlapEquiv,
      ``ManuscriptAudit.NodalGluedFieldCharts.zOverlapEquiv_algebraMap,
      ``ManuscriptAudit.NodalGluedFieldCharts.zOverlapEquiv_x,
      ``ManuscriptAudit.NodalGluedFieldCharts.zOverlapEquiv_inv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
