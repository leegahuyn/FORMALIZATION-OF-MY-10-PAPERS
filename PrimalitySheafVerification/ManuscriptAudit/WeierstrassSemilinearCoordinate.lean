import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! A field automorphism induces the literal semilinear isomorphism of a
Weierstrass coordinate ring and carries its actual point ideals accordingly. -/

namespace ManuscriptAudit.WeierstrassSemilinearCoordinate

open Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

noncomputable section

variable {K L : Type*} [Field K] [Field L]
variable (W : WeierstrassCurve.Affine K) (e : K ≃+* L)

private def polynomialEquiv : Polynomial K ≃+* Polynomial L :=
  { Polynomial.mapRingHom e.toRingHom with
    invFun := Polynomial.mapRingHom e.symm.toRingHom
    left_inv := fun p => by
      change (p.map e.toRingHom).map e.symm.toRingHom = p
      rw [Polynomial.map_map]
      have h : e.symm.toRingHom.comp e.toRingHom = RingHom.id K :=
        RingHom.ext e.symm_apply_apply
      rw [h, Polynomial.map_id]
    right_inv := fun p => by
      change (p.map e.symm.toRingHom).map e.toRingHom = p
      rw [Polynomial.map_map]
      have h : e.toRingHom.comp e.symm.toRingHom = RingHom.id L :=
        RingHom.ext e.apply_symm_apply
      rw [h, Polynomial.map_id] }

/-- The actual semilinear coordinate-ring isomorphism on the Weierstrass equation. -/
def coordinateEquiv : W.CoordinateRing ≃+* (W.map e.toRingHom).CoordinateRing :=
  AdjoinRoot.mapRingEquiv (polynomialEquiv e) W.polynomial (W.map e.toRingHom).polynomial
    (by
      change Associated (W.polynomial.map (Polynomial.mapRingHom e.toRingHom))
        (W.map e.toRingHom).polynomial
      rw [← W.map_polynomial])

theorem coordinateEquiv_toRingHom :
    (coordinateEquiv W e).toRingHom = CoordinateRing.map W e.toRingHom := rfl

theorem coordinateEquiv_XClass (x : K) :
    coordinateEquiv W e (CoordinateRing.XClass W x) =
      CoordinateRing.XClass (W.map e.toRingHom) (e x) := by
  change CoordinateRing.map W e.toRingHom (CoordinateRing.XClass W x) = _
  simp only [CoordinateRing.XClass, CoordinateRing.map_mk, Polynomial.map_C,
    Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X] <;> rfl

theorem coordinateEquiv_YClass (y : K) :
    coordinateEquiv W e (CoordinateRing.YClass W (C y)) =
      CoordinateRing.YClass (W.map e.toRingHom) (C (e y)) := by
  change CoordinateRing.map W e.toRingHom (CoordinateRing.YClass W (C y)) = _
  simp only [CoordinateRing.YClass, CoordinateRing.map_mk, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.coe_mapRingHom] <;> rfl

/-- The semilinear ring map sends the actual \((X-x,Y-y)\) ideal to the
actual ideal of the corresponding semilinearly transported point. -/
theorem coordinateEquiv_XYIdeal (x y : K) :
    Ideal.map (coordinateEquiv W e).toRingHom (CoordinateRing.XYIdeal W x (C y)) =
      CoordinateRing.XYIdeal (W.map e.toRingHom) (e x) (C (e y)) := by
  simp only [CoordinateRing.XYIdeal, Ideal.map_span, Set.image_pair]
  change Ideal.span {coordinateEquiv W e (CoordinateRing.XClass W x),
    coordinateEquiv W e (CoordinateRing.YClass W (C y))} = _
  rw [coordinateEquiv_XClass, coordinateEquiv_YClass]

end

end ManuscriptAudit.WeierstrassSemilinearCoordinate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassSemilinearCoordinate.coordinateEquiv_XYIdeal
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
