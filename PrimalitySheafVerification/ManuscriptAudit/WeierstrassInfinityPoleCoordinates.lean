import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartCoordinates
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityPuncture

/-! The original affine coordinates on the Cartier puncture have precisely
the denominators u² and u³, where u=X/Y and the bracket is a unit. -/

namespace ManuscriptAudit.WeierstrassInfinityPoleCoordinates

open Polynomial WeierstrassCurve.Affine
open WeierstrassInfinityChartAlgebra WeierstrassInfinityChartCoordinates
open WeierstrassInfinityOpenCover
open scoped Polynomial.Bivariate

noncomputable section

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev N := Neighborhood W
private abbrev P := Puncture W

def punctureX : P W := algebraMap (N W) (P W) (localX W)
def punctureZ : P W := algebraMap (N W) (P W) (localZ W)
def punctureBracket : P W :=
  algebraMap (N W) (P W) (algebraMap (WeierstrassInfinityChartAlgebra.Ring W) (N W) (bracket W))
def punctureInverse : P W := IsLocalization.Away.invSelf (localX W)

def xAffine : P W := punctureBracket W * punctureInverse W ^ 2
def yAffine : P W := punctureBracket W * punctureInverse W ^ 3

private theorem punctureX_mul_inverse : punctureX W * punctureInverse W = 1 :=
  IsLocalization.Away.mul_invSelf (localX W)

private theorem punctureRelation :
    punctureZ W * punctureBracket W = punctureX W ^ 3 := by
  let f := (algebraMap (N W) (P W)).comp
    (algebraMap (WeierstrassInfinityChartAlgebra.Ring W) (N W))
  have h := congrArg f (relation W)
  simpa only [RingHom.comp_apply, map_mul, map_pow, punctureX, punctureZ, punctureBracket,
    localX, localZ, f] using h

theorem y_is_inverse_z : punctureZ W * yAffine W = 1 := by
  rw [yAffine, ← mul_assoc, punctureRelation, ← mul_pow, punctureX_mul_inverse, one_pow]

theorem x_is_ratio : punctureX W * yAffine W = xAffine W := by
  calc
    _ = (punctureBracket W * punctureInverse W ^ 2) *
        (punctureX W * punctureInverse W) := by unfold yAffine; ring
    _ = _ := by rw [punctureX_mul_inverse, mul_one, xAffine]

theorem x_pole_equation : xAffine W * punctureX W ^ 2 = punctureBracket W := by
  rw [xAffine, mul_assoc, ← mul_pow, mul_comm (punctureInverse W), punctureX_mul_inverse,
    one_pow, mul_one]

theorem y_pole_equation : yAffine W * punctureX W ^ 3 = punctureBracket W := by
  rw [yAffine, mul_assoc, ← mul_pow, mul_comm (punctureInverse W), punctureX_mul_inverse,
    one_pow, mul_one]

theorem punctureBracket_isUnit : IsUnit (punctureBracket W) :=
  (IsLocalization.Away.algebraMap_isUnit (S := N W) (bracket W)).map
    (algebraMap (N W) (P W))

private theorem infinityEquation_puncture : infinityEquation W (punctureX W) (punctureZ W) = 0 := by
  have h := congrArg (algebraMap (WeierstrassInfinityChartAlgebra.Ring W) (P W))
    (infinity_relation W)
  simpa only [infinityEquation, punctureX, punctureZ, localX, localZ, map_add, map_sub, map_mul,
    map_pow, map_zero, ← IsScalarTower.algebraMap_apply] using h

private theorem affineEquation_puncture : affineEquation W (xAffine W) (yAffine W) = 0 := by
  rw [← x_is_ratio]
  exact infinity_to_affine W _ _ _ (infinityEquation_puncture W) (y_is_inverse_z W)

private theorem evaluation_puncture :
    W.polynomial.eval₂ (Polynomial.aeval (R := K) (xAffine W)).toRingHom (yAffine W) = 0 := by
  rw [eval_affineEquation]
  exact affineEquation_puncture W

/-- The original affine Weierstrass algebra maps to the true puncture with
the literal coordinate formulas obtained by projective rescaling. -/
def affineToPuncture : W.CoordinateRing →ₐ[K] P W :=
  AdjoinRoot.liftAlgHom W.polynomial (Polynomial.aeval (xAffine W)) (yAffine W) (evaluation_puncture W)

theorem affineToPuncture_x : affineToPuncture W (affineX W) = xAffine W :=
  (AdjoinRoot.liftAlgHom_of W.polynomial (Polynomial.aeval (R := K) (xAffine W))
    (yAffine W) (evaluation_puncture W) X).trans (Polynomial.aeval_X _)

theorem affineToPuncture_y : affineToPuncture W (affineY W) = yAffine W :=
  AdjoinRoot.liftAlgHom_root W.polynomial (Polynomial.aeval (R := K) (xAffine W))
    (yAffine W) (evaluation_puncture W)

end

end ManuscriptAudit.WeierstrassInfinityPoleCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityPoleCoordinates.x_pole_equation,
      ``ManuscriptAudit.WeierstrassInfinityPoleCoordinates.y_pole_equation,
      ``ManuscriptAudit.WeierstrassInfinityPoleCoordinates.punctureBracket_isUnit,
      ``ManuscriptAudit.WeierstrassInfinityPoleCoordinates.affineToPuncture_x,
      ``ManuscriptAudit.WeierstrassInfinityPoleCoordinates.affineToPuncture_y] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
