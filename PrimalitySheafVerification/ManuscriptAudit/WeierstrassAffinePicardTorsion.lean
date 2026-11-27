import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.PicardGroup
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-!
# The actual affine Picard group of a Weierstrass curve

A nonsingular point gives its invertible ideal class on the literal affine
coordinate ring. The same map embeds every finite torsion level and the
native Tate module into the corresponding torsion of the Picard group.
-/

namespace ManuscriptAudit.WeierstrassAffinePicardTorsion

open WeierstrassCurve.Affine
open TorsionFrobeniusModule PowerTorsionTower PowerTateModule

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-- Send a point to its invertible ideal's class in the coordinate-ring Picard group. -/
def pointToPicard : W.Point →+ Additive (CommRing.Pic W.CoordinateRing) :=
  (ClassGroup.equivPic W.CoordinateRing).toAdditive.toAddMonoidHom.comp
    (Point.toClass (W := W))

theorem pointToPicard_injective : Function.Injective (pointToPicard W) :=
  (ClassGroup.equivPic W.CoordinateRing).toAdditive.injective.comp Point.toClass_injective

/-- The genuine point-map injection on ℓ-power torsion, before taking a limit. -/
def powerTorsionToPicard (l n : ℕ) :
    PowerTorsion l W.Point n →+ PowerTorsion l (Additive (CommRing.Pic W.CoordinateRing)) n :=
  mapAdd (l ^ n) (pointToPicard W)

theorem powerTorsionToPicard_injective (l n : ℕ) :
    Function.Injective (powerTorsionToPicard W l n) := by
  change Function.Injective (mapLinear (l ^ n) (pointToPicard W))
  exact mapLinear_injective (l ^ n) _ (pointToPicard_injective W)

theorem powerTorsionToPicard_transition (l n : ℕ) (x : PowerTorsion l W.Point (n + 1)) :
    transition l (Additive (CommRing.Pic W.CoordinateRing)) n (powerTorsionToPicard W l (n + 1) x) =
      powerTorsionToPicard W l n (transition l W.Point n x) :=
  map_transition l (pointToPicard W) n x

/-- The affine Picard inverse limit receives the genuine geometric point Tate module. -/
def tateToPicard (l : ℕ) [Fact l.Prime] :
    Tate l W.Point →ₗ[ℤ_[l]] Tate l (Additive (CommRing.Pic W.CoordinateRing)) :=
  map l (pointToPicard W)

theorem tateToPicard_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (tateToPicard W l) :=
  map_injective l _ (pointToPicard_injective W)

end

end ManuscriptAudit.WeierstrassAffinePicardTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassAffinePicardTorsion.pointToPicard_injective,
      ``ManuscriptAudit.WeierstrassAffinePicardTorsion.powerTorsionToPicard_injective,
      ``ManuscriptAudit.WeierstrassAffinePicardTorsion.powerTorsionToPicard_transition,
      ``ManuscriptAudit.WeierstrassAffinePicardTorsion.tateToPicard_injective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
