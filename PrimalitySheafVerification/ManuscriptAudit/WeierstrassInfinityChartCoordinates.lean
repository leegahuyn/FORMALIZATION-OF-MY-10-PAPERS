import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartAlgebra

/-! Coordinate equations used to compare the Y and Z charts of a Weierstrass curve. -/

namespace ManuscriptAudit.WeierstrassInfinityChartCoordinates

open Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

universe u v

noncomputable section

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

def affineX : W.CoordinateRing := CoordinateRing.mk W (C X)
def affineY : W.CoordinateRing := CoordinateRing.mk W Y

variable {L : Type v} [CommRing L] [Algebra K L]

/-- The affine Z=1 relation at two coordinates in a coefficient algebra. -/
def affineEquation (x y : L) : L :=
  y ^ 2 + algebraMap K L W.a₁ * x * y + algebraMap K L W.a₃ * y -
    (x ^ 3 + algebraMap K L W.a₂ * x ^ 2 + algebraMap K L W.a₄ * x + algebraMap K L W.a₆)

/-- The affine Y=1 relation at two coordinates in a coefficient algebra. -/
def infinityEquation (u v : L) : L :=
  v + algebraMap K L W.a₁ * u * v + algebraMap K L W.a₃ * v ^ 2 -
    (u ^ 3 + algebraMap K L W.a₂ * u ^ 2 * v + algebraMap K L W.a₄ * u * v ^ 2 +
      algebraMap K L W.a₆ * v ^ 3)

theorem eval_affineEquation (x y : L) :
    W.polynomial.eval₂ (Polynomial.aeval (R := K) x).toRingHom y = affineEquation W x y := by
  let f := (Polynomial.aeval (R := K) x).toRingHom
  have hX : f X = x := Polynomial.aeval_X x
  have hC (a : K) : f (C a) = algebraMap K L a := Polynomial.aeval_C _ _
  change W.polynomial.eval₂ f y = affineEquation W x y
  simp only [WeierstrassCurve.Affine.polynomial, affineEquation, Polynomial.eval₂_add,
    Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X, map_add, map_mul, map_pow, hC, hX]
  ring

theorem eval_infinityEquation (u v : L) :
    (WeierstrassInfinityChartAlgebra.equation W).eval₂ (Polynomial.aeval (R := K) u).toRingHom v =
      infinityEquation W u v := by
  let f := (Polynomial.aeval (R := K) u).toRingHom
  have hX : f X = u := Polynomial.aeval_X u
  have hC (a : K) : f (C a) = algebraMap K L a := Polynomial.aeval_C _ _
  change (WeierstrassInfinityChartAlgebra.equation W).eval₂ f v = infinityEquation W u v
  simp only [WeierstrassInfinityChartAlgebra.equation, WeierstrassInfinityChartAlgebra.bracketPolynomial,
    infinityEquation, Polynomial.eval₂_one, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    map_add, map_mul, map_pow, hC, hX]
  ring

private theorem affine_constant (a : K) :
    algebraMap K W.CoordinateRing a = CoordinateRing.mk W (C (C a)) := rfl

theorem affine_relation : affineEquation W (affineX W) (affineY W) = 0 := by
  have h : CoordinateRing.mk W W.polynomial = 0 := AdjoinRoot.mk_self
  simp only [WeierstrassCurve.Affine.polynomial, map_add, map_sub, map_mul, map_pow] at h
  simp only [affineEquation, affineX, affineY, affine_constant]
  linear_combination h

private theorem infinity_constant (a : K) :
    algebraMap K (WeierstrassInfinityChartAlgebra.Ring W) a =
      AdjoinRoot.mk (WeierstrassInfinityChartAlgebra.equation W) (C (C a)) := rfl

theorem infinity_relation :
    infinityEquation W (WeierstrassInfinityChartAlgebra.x W) (WeierstrassInfinityChartAlgebra.z W) = 0 := by
  have h : AdjoinRoot.mk (WeierstrassInfinityChartAlgebra.equation W)
      (WeierstrassInfinityChartAlgebra.equation W) = 0 := AdjoinRoot.mk_self
  change AdjoinRoot.mk (WeierstrassInfinityChartAlgebra.equation W)
    (Y * WeierstrassInfinityChartAlgebra.bracketPolynomial W - (C X) ^ 3) = 0 at h
  rw [map_sub, map_mul, map_pow] at h
  unfold WeierstrassInfinityChartAlgebra.bracketPolynomial at h
  simp only [map_add, map_sub, map_mul, map_pow, map_one] at h
  simp only [infinityEquation, WeierstrassInfinityChartAlgebra.x, WeierstrassInfinityChartAlgebra.z,
    infinity_constant]
  linear_combination h

/-- Replacing (x,y) by (x/y,1/y) sends a point of Z=1 to the Y=1 equation. -/
theorem affine_to_infinity (x y b : L) (h : affineEquation W x y = 0) (hb : y * b = 1) :
    infinityEquation W (x * b) b = 0 := by
  unfold affineEquation at h
  unfold infinityEquation
  linear_combination b ^ 3 * h -
    (b * (y * b + 1) + (algebraMap K L W.a₁ * x + algebraMap K L W.a₃) * b ^ 2) * hb

/-- Replacing (u,v) by (u/v,1/v) sends a point of Y=1 to the Z=1 equation. -/
theorem infinity_to_affine (u v b : L) (h : infinityEquation W u v = 0) (hb : v * b = 1) :
    affineEquation W (u * b) b = 0 := by
  unfold infinityEquation at h
  unfold affineEquation
  linear_combination b ^ 3 * h -
    (b ^ 2 * (1 + algebraMap K L W.a₁ * u - algebraMap K L W.a₂ * u ^ 2) +
      b * (algebraMap K L W.a₃ - algebraMap K L W.a₄ * u) * (v * b + 1) -
      algebraMap K L W.a₆ * ((v * b) ^ 2 + v * b + 1)) * hb

end

end ManuscriptAudit.WeierstrassInfinityChartCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityChartCoordinates.eval_affineEquation,
      ``ManuscriptAudit.WeierstrassInfinityChartCoordinates.eval_infinityEquation,
      ``ManuscriptAudit.WeierstrassInfinityChartCoordinates.affine_relation,
      ``ManuscriptAudit.WeierstrassInfinityChartCoordinates.infinity_relation,
      ``ManuscriptAudit.WeierstrassInfinityChartCoordinates.affine_to_infinity,
      ``ManuscriptAudit.WeierstrassInfinityChartCoordinates.infinity_to_affine] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
