import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassArithmeticFrobeniusScheme
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassSemilinearCoordinate

/-! On the actual affine chart, the semilinear scheme Frobenius is
the Spec morphism of the literal coordinate-ring automorphism. -/

namespace ManuscriptAudit.WeierstrassArithmeticCoordinateFrobenius

open AlgebraicGeometry CategoryTheory Polynomial WeierstrassCurve.Affine
open WeierstrassProjectiveClosure WeierstrassArithmeticFrobeniusScheme
open WeierstrassSemilinearCoordinate

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private def coordinateTransport {K : Type} [Field K] {U V : WeierstrassCurve.Affine K} (h : U = V) :
    U.CoordinateRing ≃+* V.CoordinateRing := by
  subst V
  exact RingEquiv.refl _

private theorem spec_coordinateTransport {K : Type} [Field K] {U V : WeierstrassCurve.Affine K}
    (h : U = V) :
    Spec.map (CommRingCat.ofHom (coordinateTransport h).toRingHom) =
      ((eqToIso (congrArg (fun W => affineScheme W) h)).symm).hom := by
  subst V
  change Spec.map (𝟙 (CommRingCat.of U.CoordinateRing)) = 𝟙 (affineScheme U)
  rw [Spec.map_id]

private theorem ideal_coordinateTransport {K : Type} [Field K] {U V : WeierstrassCurve.Affine K}
    (h : U = V) (x y : K) :
    Ideal.map (coordinateTransport h).toRingHom (CoordinateRing.XYIdeal U x (C y)) =
      CoordinateRing.XYIdeal V x (C y) := by
  subst V
  change Ideal.map (RingHom.id _) _ = _
  simp

variable (k K : Type) [Field k] [Fintype k] [Field K] [Algebra k K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine k)

private abbrev V {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := W.baseChange K
private abbrev σ := fieldFrobenius k K

private theorem fixed :
    (V K W).map (σ k K).toRingHom = V K W := by
  rw [fieldFrobenius_toRingHom]
  exact W.map_baseChange (FiniteField.frobeniusAlgHom k K)

/-- The arithmetic Frobenius on actual affine coordinates. -/
def coordinateFrobenius : (V K W).CoordinateRing ≃+* (V K W).CoordinateRing :=
  (coordinateEquiv (V K W) (σ k K)).trans (coordinateTransport (fixed k K W))

/-- The spectrum map of the literal coordinate-ring automorphism is
the actual affine chart restriction of the projective Frobenius. -/
theorem spec_coordinateFrobenius :
    Spec.map (CommRingCat.ofHom (coordinateFrobenius k K W).toRingHom) =
      (affineFrobenius k K W).hom := by
  let e := CommRingCat.ofHom (coordinateEquiv (V K W) (σ k K)).toRingHom
  let t := CommRingCat.ofHom (coordinateTransport (fixed k K W)).toRingHom
  change Spec.map (e ≫ t) =
    ((eqToIso (congrArg (fun Z => affineScheme Z) (fixed k K W))).symm).hom ≫ Spec.map e
  rw [Spec.map_comp, spec_coordinateTransport]

/-- The actual affine Frobenius takes the ideal of a point to the ideal
of its true arithmetic Frobenius coordinates. -/
theorem coordinateFrobenius_pointIdeal (x y : K) :
    Ideal.map (coordinateFrobenius k K W).toRingHom (CoordinateRing.XYIdeal (V K W) x (C y)) =
      CoordinateRing.XYIdeal (V K W)
        ((FiniteField.frobeniusAlgHom k K) x) (C ((FiniteField.frobeniusAlgHom k K) y)) := by
  let e := coordinateEquiv (V K W) (σ k K)
  let t := coordinateTransport (fixed k K W)
  change Ideal.map (t.toRingHom.comp e.toRingHom) (CoordinateRing.XYIdeal (V K W) x (C y)) = _
  rw [← Ideal.map_map, coordinateEquiv_XYIdeal, ideal_coordinateTransport] <;> rfl

end

end ManuscriptAudit.WeierstrassArithmeticCoordinateFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassArithmeticCoordinateFrobenius.spec_coordinateFrobenius,
      ``ManuscriptAudit.WeierstrassArithmeticCoordinateFrobenius.coordinateFrobenius_pointIdeal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
