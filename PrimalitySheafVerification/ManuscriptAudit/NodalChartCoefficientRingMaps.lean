import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalChartEquationMaps

/-! The actual coefficient maps preserve both coordinates of each nodal chart. -/

namespace ManuscriptAudit.NodalChartCoefficientMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open NodalIntegralChartTransition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 170000
set_option synthInstance.maxHeartbeats 14000

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def rootRingCongr {p q : Polynomial (Polynomial S)} (h : p = q) :
    AdjoinRoot p ≃ₐ[S] AdjoinRoot q :=
  AdjoinRoot.algEquivOfEq S p q h

private theorem rootRingCongr_of {p q : Polynomial (Polynomial S)} (h : p = q)
    (a : Polynomial S) : rootRingCongr S h (AdjoinRoot.of p a) = AdjoinRoot.of q a := by
  rw [rootRingCongr, AdjoinRoot.coe_algEquivOfEq, AdjoinRoot.coe_algHomOfDvd,
    AdjoinRoot.liftAlgHom_of] <;> rfl

private theorem rootRingCongr_root {p q : Polynomial (Polynomial S)} (h : p = q) :
    rootRingCongr S h (AdjoinRoot.root p) = AdjoinRoot.root q :=
  AdjoinRoot.algEquivOfEq_root S p q h

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


end
end ManuscriptAudit.NodalChartCoefficientMaps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalChartCoefficientMaps.zRingMap_x,
      ``ManuscriptAudit.NodalChartCoefficientMaps.zRingMap_y,
      ``ManuscriptAudit.NodalChartCoefficientMaps.yRingMap_x,
      ``ManuscriptAudit.NodalChartCoefficientMaps.yRingMap_z,
      ``ManuscriptAudit.NodalChartCoefficientMaps.zRingMap_algebraMap,
      ``ManuscriptAudit.NodalChartCoefficientMaps.yRingMap_algebraMap] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
