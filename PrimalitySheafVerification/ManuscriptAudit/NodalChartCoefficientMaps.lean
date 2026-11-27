import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PlaneEquationBaseChange
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralChartTransition

/-! Coefficient extension of the two displayed charts of the nodal cubic.
The maps carry the actual coordinate functions to the same coordinates
in the new coefficient ring, and each chart square is a scheme pullback. -/

namespace ManuscriptAudit.NodalChartCoefficientMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open NodalIntegralChartTransition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private theorem zEquation_map :
    PlaneEquationBaseChange.equation R S (zEquation R) = zEquation S := by
  simp only [PlaneEquationBaseChange.equation, zEquation, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  have h : PlaneEquationBaseChange.coeffMap R S ((X : Polynomial R) ^ 2 * (X + 1)) =
      X ^ 2 * (X + 1) := by
    change ((X : Polynomial R) ^ 2 * (X + 1)).map (algebraMap R S) =
      (X : Polynomial S) ^ 2 * (X + 1)
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_add,
      Polynomial.map_one]
  rw [h]

private theorem yEquation_map :
    PlaneEquationBaseChange.equation R S (yEquation R) = yEquation S := by
  simp only [PlaneEquationBaseChange.equation, yEquation, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  have hx : PlaneEquationBaseChange.coeffMap R S (X : Polynomial R) = X :=
    Polynomial.map_X _
  have hq : PlaneEquationBaseChange.coeffMap R S ((X : Polynomial R) ^ 2) = X ^ 2 := by
    rw [map_pow, hx]
  rw [hx, hq]

private def rootRingCongr {p q : Polynomial (Polynomial S)} (h : p = q) :
    AdjoinRoot p ≃ₐ[S] AdjoinRoot q := by
  subst q
  exact .refl

private theorem rootRingCongr_of {p q : Polynomial (Polynomial S)} (h : p = q)
    (a : Polynomial S) : rootRingCongr S h (AdjoinRoot.of p a) = AdjoinRoot.of q a := by
  subst q
  rfl

private theorem rootRingCongr_root {p q : Polynomial (Polynomial S)} (h : p = q) :
    rootRingCongr S h (AdjoinRoot.root p) = AdjoinRoot.root q := by
  subst q
  rfl

private def zIso := rootRingCongr S (zEquation_map R S)
private def yIso := rootRingCongr S (yEquation_map R S)

def zRingMap : zChart R →+* zChart S :=
  (zIso R S).toRingHom.comp (PlaneEquationBaseChange.ringMap R S (zEquation R))

def yRingMap : yChart R →+* yChart S :=
  (yIso R S).toRingHom.comp (PlaneEquationBaseChange.ringMap R S (yEquation R))

theorem zRingMap_of (a : Polynomial R) :
    zRingMap R S (AdjoinRoot.of (zEquation R) a) =
      AdjoinRoot.of (zEquation S) (PlaneEquationBaseChange.coeffMap R S a) := by
  change zIso R S (PlaneEquationBaseChange.ringMap R S (zEquation R)
    (AdjoinRoot.of (zEquation R) a)) = _
  rw [PlaneEquationBaseChange.ringMap_of]
  exact rootRingCongr_of S _ _

theorem yRingMap_of (a : Polynomial R) :
    yRingMap R S (AdjoinRoot.of (yEquation R) a) =
      AdjoinRoot.of (yEquation S) (PlaneEquationBaseChange.coeffMap R S a) := by
  change yIso R S (PlaneEquationBaseChange.ringMap R S (yEquation R)
    (AdjoinRoot.of (yEquation R) a)) = _
  rw [PlaneEquationBaseChange.ringMap_of]
  exact rootRingCongr_of S _ _

@[simp] theorem zRingMap_x : zRingMap R S (xZ R) = xZ S := by
  unfold xZ
  rw [zRingMap_of]
  exact congrArg (AdjoinRoot.of (zEquation S)) (Polynomial.map_X (algebraMap R S))

@[simp] theorem yRingMap_x : yRingMap R S (xY R) = xY S := by
  unfold xY
  rw [yRingMap_of]
  exact congrArg (AdjoinRoot.of (yEquation S)) (Polynomial.map_X (algebraMap R S))

@[simp] theorem zRingMap_y : zRingMap R S (yZ R) = yZ S := by
  change zIso R S (PlaneEquationBaseChange.ringMap R S (zEquation R)
    (AdjoinRoot.root (zEquation R))) = _
  rw [PlaneEquationBaseChange.ringMap_root]
  exact rootRingCongr_root S _

@[simp] theorem yRingMap_z : yRingMap R S (zY R) = zY S := by
  change yIso R S (PlaneEquationBaseChange.ringMap R S (yEquation R)
    (AdjoinRoot.root (yEquation R))) = _
  rw [PlaneEquationBaseChange.ringMap_root]
  exact rootRingCongr_root S _

theorem zRingMap_algebraMap (a : R) :
    zRingMap R S (algebraMap R (zChart R) a) =
      algebraMap S (zChart S) (algebraMap R S a) := by
  change zRingMap R S (AdjoinRoot.of (zEquation R) (C a)) =
    AdjoinRoot.of (zEquation S) (C (algebraMap R S a))
  rw [zRingMap_of]
  exact congrArg (AdjoinRoot.of (zEquation S)) (Polynomial.map_C (algebraMap R S))

theorem yRingMap_algebraMap (a : R) :
    yRingMap R S (algebraMap R (yChart R) a) =
      algebraMap S (yChart S) (algebraMap R S a) := by
  change yRingMap R S (AdjoinRoot.of (yEquation R) (C a)) =
    AdjoinRoot.of (yEquation S) (C (algebraMap R S a))
  rw [yRingMap_of]
  exact congrArg (AdjoinRoot.of (yEquation S)) (Polynomial.map_C (algebraMap R S))

private theorem cast_map_isPullback {p : Polynomial (Polynomial R)}
    {q : Polynomial (Polynomial S)} (h : PlaneEquationBaseChange.equation R S p = q) :
    IsPullback (PlaneEquationBaseChange.structureMap S q)
      (Spec.map (CommRingCat.ofHom ((rootRingCongr S h).toRingHom.comp
        (PlaneEquationBaseChange.ringMap R S p))))
      (PlaneEquationBaseChange.changeBase R S) (PlaneEquationBaseChange.structureMap R p) := by
  subst q
  exact PlaneEquationBaseChange.square_isPullback R S p

theorem zSquare_isPullback :
    IsPullback (PlaneEquationBaseChange.structureMap S (zEquation S))
      (Spec.map (CommRingCat.ofHom (zRingMap R S))) (PlaneEquationBaseChange.changeBase R S)
      (PlaneEquationBaseChange.structureMap R (zEquation R)) :=
  cast_map_isPullback R S (zEquation_map R S)

theorem ySquare_isPullback :
    IsPullback (PlaneEquationBaseChange.structureMap S (yEquation S))
      (Spec.map (CommRingCat.ofHom (yRingMap R S))) (PlaneEquationBaseChange.changeBase R S)
      (PlaneEquationBaseChange.structureMap R (yEquation R)) :=
  cast_map_isPullback R S (yEquation_map R S)

end
end ManuscriptAudit.NodalChartCoefficientMaps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalChartCoefficientMaps.zRingMap_x,
      ``ManuscriptAudit.NodalChartCoefficientMaps.yRingMap_x,
      ``ManuscriptAudit.NodalChartCoefficientMaps.zRingMap_y,
      ``ManuscriptAudit.NodalChartCoefficientMaps.yRingMap_z,
      ``ManuscriptAudit.NodalChartCoefficientMaps.zSquare_isPullback,
      ``ManuscriptAudit.NodalChartCoefficientMaps.ySquare_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
