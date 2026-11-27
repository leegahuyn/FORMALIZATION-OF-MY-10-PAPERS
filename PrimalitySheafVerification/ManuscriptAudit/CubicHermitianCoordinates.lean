import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.FiniteFieldPointCount
import PrimalitySheafVerification.ManuscriptAudit.HermitianTangentIdealMembership

/-! Normalized coordinates in the native affine coordinate ring of y² = x³ + A. -/

namespace ManuscriptAudit.CubicHermitianCoordinates

open Polynomial WeierstrassCurve FiniteFieldPointCount
open HermitianTangentIdealMembership
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K]

abbrev Centered (A : K) : WeierstrassCurve.Affine K :=
  (shortCubic (0 : K) A).toProjective.toAffine

def xCoord (A : K) : (Centered A).CoordinateRing :=
  Affine.CoordinateRing.mk (Centered A) (C X)

def yCoord (A : K) : (Centered A).CoordinateRing :=
  Affine.CoordinateRing.mk (Centered A) Y

private theorem mk_CC (A r : K) :
    Affine.CoordinateRing.mk (Centered A) (C (C r)) =
      algebraMap K (Centered A).CoordinateRing r := rfl

theorem coordinate_equation (A : K) :
    yCoord A ^ 2 = xCoord A ^ 3 + algebraMap K (Centered A).CoordinateRing A := by
  let W := Centered A
  have hp : W.polynomial = Y ^ 2 - C (X ^ 3 + C A) := by
    simp [W, Centered, shortCubic, Affine.polynomial]
  have h := AdjoinRoot.mk_self W.polynomial
  change Affine.CoordinateRing.mk W W.polynomial = 0 at h
  rw [hp, C_add, C_pow, map_sub, map_add, map_pow, map_pow] at h
  change yCoord A ^ 2 - (xCoord A ^ 3 + Affine.CoordinateRing.mk W (C (C A))) = 0 at h
  rw [mk_CC] at h
  exact sub_eq_zero.mp h

theorem normalized_equation {D : Type*} [CommRing D] [Algebra K D]
    {A α β : K} (hA : A ≠ 0) (hα : α ^ 3 = -A) (hβ : β ^ 2 = A)
    {X Y : D} (hXY : Y ^ 2 = X ^ 3 + algebraMap K D A) :
    (algebraMap K D α⁻¹ * X) ^ 3 + (algebraMap K D β⁻¹ * Y) ^ 2 = 1 := by
  have ha : α⁻¹ ^ 3 = -(A⁻¹) := by rw [inv_pow, hα, inv_neg]
  have hb : β⁻¹ ^ 2 = A⁻¹ := by rw [inv_pow, hβ]
  have hUnit : algebraMap K D A⁻¹ * algebraMap K D A = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hA, map_one]
  rw [mul_pow, mul_pow, ← map_pow, ← map_pow, ha, hb, map_neg, hXY]
  linear_combination hUnit

def normalizedX (A α : K) : (Centered A).CoordinateRing :=
  algebraMap K (Centered A).CoordinateRing α⁻¹ * xCoord A

def normalizedY (A β : K) : (Centered A).CoordinateRing :=
  algebraMap K (Centered A).CoordinateRing β⁻¹ * yCoord A

theorem normalized_coordinate_equation {A α β : K}
    (hA : A ≠ 0) (hα : α ^ 3 = -A) (hβ : β ^ 2 = A) :
    normalizedX A α ^ 3 + normalizedY A β ^ 2 = 1 :=
  normalized_equation hA hα hβ (coordinate_equation A)

private theorem xClass_eq (A x : K) :
    Affine.CoordinateRing.XClass (Centered A) x =
      xCoord A - algebraMap K (Centered A).CoordinateRing x := by
  unfold Affine.CoordinateRing.XClass xCoord
  rw [C_sub, map_sub, mk_CC]

private theorem yClass_eq (A y : K) :
    Affine.CoordinateRing.YClass (Centered A) (C y) =
      yCoord A - algebraMap K (Centered A).CoordinateRing y := by
  unfold Affine.CoordinateRing.YClass yCoord
  rw [map_sub, mk_CC]

/-- Scaling the two generators by the normalization units preserves the native point ideal. -/
theorem normalized_pointIdeal (A : K) {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) (x y : K) :
    pointIdeal (normalizedX A α) (normalizedY A β)
      (algebraMap K (Centered A).CoordinateRing (α⁻¹ * x))
      (algebraMap K (Centered A).CoordinateRing (β⁻¹ * y)) =
        Affine.CoordinateRing.XYIdeal (Centered A) x (C y) := by
  rw [pointIdeal, Affine.CoordinateRing.XYIdeal, Ideal.span_insert, Ideal.span_insert,
    xClass_eq A x, yClass_eq A y]
  unfold normalizedX normalizedY
  simp only [map_mul, ← mul_sub]
  rw [Ideal.span_singleton_mul_left_unit ((IsUnit.mk0 _ (inv_ne_zero hα)).map (algebraMap K _)),
    Ideal.span_singleton_mul_left_unit ((IsUnit.mk0 _ (inv_ne_zero hβ)).map (algebraMap K _))]

end
end ManuscriptAudit.CubicHermitianCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicHermitianCoordinates.coordinate_equation,
      ``ManuscriptAudit.CubicHermitianCoordinates.normalized_coordinate_equation,
      ``ManuscriptAudit.CubicHermitianCoordinates.normalized_pointIdeal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
