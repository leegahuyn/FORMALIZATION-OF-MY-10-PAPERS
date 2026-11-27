import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Principal products of point ideals give actual relations in the Weierstrass group. -/

namespace ManuscriptAudit.AffinePointPrincipalRelation

open WeierstrassCurve Polynomial
open scoped nonZeroDivisors

noncomputable section

theorem ideal_product_principal_of_faithfullyFlat {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] (I J : Ideal R) (n : ℕ) (f : R)
    (h : I.map (algebraMap R S) ^ n * J.map (algebraMap R S) =
      Ideal.span {algebraMap R S f}) :
    I ^ n * J = Ideal.span {f} := by
  apply Ideal.map_injective_of_faithfullyFlat (A := R) (B := S)
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_span, Set.image_singleton]
  exact h

variable {K : Type*} [Field K] [DecidableEq K] {W : Affine K}

/-- The native group equation associated to a principal product of two point ideals. -/
theorem nsmul_add_eq_zero_of_principal {x y a b : K}
    (hP : W.Nonsingular x y) (hQ : W.Nonsingular a b)
    (n : ℕ) (f : W.CoordinateRing)
    (h : Affine.CoordinateRing.XYIdeal W x (C y) ^ n *
      Affine.CoordinateRing.XYIdeal W a (C b) = Ideal.span {f}) :
    (n : ℕ) • (Affine.Point.some x y hP : W.Point) + Affine.Point.some a b hQ = 0 := by
  let P := Affine.CoordinateRing.XYIdeal' (W := W) hP
  let Q := Affine.CoordinateRing.XYIdeal' (W := W) hQ
  let A := Affine.CoordinateRing.XYIdeal W x (C y)
  let B := Affine.CoordinateRing.XYIdeal W a (C b)
  let U := P ^ n * Q
  have hU : (U : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      ((A ^ n * B : Ideal W.CoordinateRing) : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
    dsimp only [U, P, Q, A, B]
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Affine.CoordinateRing.XYIdeal'_eq,
      Affine.CoordinateRing.XYIdeal'_eq, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  have hProd : A ^ n * B = Ideal.span {f} := h
  have hf : f ≠ 0 := by
    intro hz
    have hzU : (U : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = 0 := by
      rw [hU, hProd, hz]
      simp
    exact Units.ne_zero U hzU
  have hc : ClassGroup.mk W.FunctionField U = 1 :=
    (ClassGroup.mk_eq_one_of_coe_ideal hU).mpr ⟨f, hf, hProd⟩
  apply (Affine.Point.toClass_eq_zero _).mp
  rw [map_add, map_nsmul, Affine.Point.toClass_some, Affine.Point.toClass_some]
  change ClassGroup.mk W.FunctionField P ^ n * ClassGroup.mk W.FunctionField Q = 1
  rw [← map_pow, ← map_mul]
  exact hc

end
end ManuscriptAudit.AffinePointPrincipalRelation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.AffinePointPrincipalRelation.ideal_product_principal_of_faithfullyFlat,
      ``ManuscriptAudit.AffinePointPrincipalRelation.nsmul_add_eq_zero_of_principal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
