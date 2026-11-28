import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityFunctionField
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityAdicOrder

/-! The projective generic-point chart and the adic order use the same
function-field map, as follows from the literal projective coordinates. -/

namespace ManuscriptAudit.WeierstrassInfinityFieldCoordinateComparison

open WeierstrassInfinityFunctionField WeierstrassInfinityAdicOrder
open WeierstrassInfinityChartAlgebra WeierstrassInfinityChartCoordinates
open WeierstrassInfinityChartOverlap WeierstrassInfinityPoleCoordinates
open WeierstrassInfinityPuncture

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev C := WeierstrassInfinityChartAlgebra.Ring W
private abbrev N := Neighborhood W
private abbrev F := W.FunctionField
private abbrev G := FractionRing (N W)
private abbrev j := algebraMap W.CoordinateRing (F W)
private abbrev n := algebraMap (N W) (G W)
private abbrev e := functionFieldEquiv W
private abbrev f := functionFieldMap W

private theorem chart_field_z : j W (affineY W) * yChartToFunctionField W (z W) = 1 := by
  have h := congrArg (affineOverlapToFunctionField W) (zy_mul_zInv W)
  change affineOverlapToFunctionField W
      ((algebraMap W.CoordinateRing (ZOverlap W) (affineY W)) * zInv W) =
    affineOverlapToFunctionField W 1 at h
  rw [map_mul, map_one, affineOverlapToFunctionField_base] at h
  change j W (affineY W) * affineOverlapToFunctionField W (toZChart W (z W)) = 1
  rw [toZChart_z]
  exact h

private theorem chart_field_x :
    yChartToFunctionField W (x W) = j W (affineX W) * yChartToFunctionField W (z W) := by
  change affineOverlapToFunctionField W (toZChart W (x W)) =
    j W (affineX W) * affineOverlapToFunctionField W (toZChart W (z W))
  rw [toZChart_x, toZChart_z, map_mul]
  exact congrArg (fun a => a * affineOverlapToFunctionField W (zInv W))
    (affineOverlapToFunctionField_base W (affineX W))

private theorem chart_neighborhood_inverse_y : e W (j W (affineY W)) * n W (localZ W) = 1 := by
  have h := congrArg (e W) (chart_field_z W)
  rw [map_mul, map_one, functionFieldEquiv_yChart] at h
  exact h

private theorem adic_neighborhood_inverse_y : n W (localZ W) * f W (j W (affineY W)) = 1 := by
  have h := congrArg (punctureToLocalFractionField W) (y_is_inverse_z W)
  rw [map_mul, map_one] at h
  rw [functionFieldMap_base, affineToPuncture_y]
  exact (congrArg (fun a => a * punctureToLocalFractionField W (yAffine W))
    (punctureToLocalFractionField_base W (localZ W)).symm).trans h

private theorem maps_y : e W (j W (affineY W)) = f W (j W (affineY W)) := by
  calc
    _ = e W (j W (affineY W)) * (n W (localZ W) * f W (j W (affineY W))) := by
      rw [adic_neighborhood_inverse_y, mul_one]
    _ = (e W (j W (affineY W)) * n W (localZ W)) * f W (j W (affineY W)) :=
      (mul_assoc _ _ _).symm
    _ = _ := by rw [chart_neighborhood_inverse_y, one_mul]

private theorem maps_x : e W (j W (affineX W)) = f W (j W (affineX W)) := by
  have h := congrArg (e W) (chart_field_x W)
  rw [functionFieldEquiv_yChart, map_mul, functionFieldEquiv_yChart] at h
  have hc : e W (j W (affineX W)) * n W (localZ W) = n W (localX W) := h.symm
  have h' := congrArg (punctureToLocalFractionField W) (x_is_ratio W)
  rw [map_mul] at h'
  have hd : f W (j W (affineX W)) = n W (localX W) * f W (j W (affineY W)) := by
    rw [functionFieldMap_base, functionFieldMap_base, affineToPuncture_x, affineToPuncture_y]
    exact h'.symm.trans (congrArg (fun a => a * punctureToLocalFractionField W (yAffine W))
      (punctureToLocalFractionField_base W (localX W)))
  rw [← maps_y] at hd
  calc
    _ = e W (j W (affineX W)) * (n W (localZ W) * e W (j W (affineY W))) := by
      rw [mul_comm (n W (localZ W)), chart_neighborhood_inverse_y, mul_one]
    _ = _ := by rw [← mul_assoc, hc, hd]

private theorem maps_constant (a : K) :
    e W (j W (algebraMap K W.CoordinateRing a)) =
      f W (j W (algebraMap K W.CoordinateRing a)) := by
  have hc : yChartToFunctionField W (algebraMap K (C W) a) =
      j W (algebraMap K W.CoordinateRing a) := by
    change affineOverlapToFunctionField W (toZChart W (algebraMap K (C W) a)) = _
    rw [(toZChart W).commutes, IsScalarTower.algebraMap_apply K W.CoordinateRing (ZOverlap W),
      affineOverlapToFunctionField_base]
  rw [← hc, functionFieldEquiv_yChart, hc, functionFieldMap_base, (affineToPuncture W).commutes]
  rw [IsScalarTower.algebraMap_apply K (N W) (Puncture W), punctureToLocalFractionField_base,
    ← IsScalarTower.algebraMap_apply K (C W) (N W)]

/-- The function-field isomorphism used by the actual projective generic
point equals the homomorphism used to compute the genuine infinity valuation. -/
theorem functionFieldEquiv_toRingHom_eq :
    (e W).toRingHom = f W := by
  apply IsFractionRing.ringHom_ext (A := W.CoordinateRing)
  intro a
  have h : (e W).toRingHom.comp (j W) = (f W).comp (j W) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext
        exact maps_constant W
      · exact maps_x W
    · exact maps_y W
  exact RingHom.congr_fun h a

end

end ManuscriptAudit.WeierstrassInfinityFieldCoordinateComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassInfinityFieldCoordinateComparison.functionFieldEquiv_toRingHom_eq
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
