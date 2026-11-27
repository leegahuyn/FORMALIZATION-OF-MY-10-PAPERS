import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralGluing
import PrimalitySheafVerification.ManuscriptAudit.NodalAffinePresentation
import PrimalitySheafVerification.ManuscriptAudit.NodalAwayNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartImmersion

/-! Exact affine coordinate identifications between the literal nodal gluing and the field model. -/

namespace ManuscriptAudit.NodalGluedFieldCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralChartTransition NodalIntegralGluing
open NodalYChartImmersion (nodeYChart yCoordinateRing xCoeff zCoeff)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 190000
set_option synthInstance.maxHeartbeats 16000

universe u
variable (K : Type u) [Field K]

def zChartEquiv : zChart K ≃ₐ[K] NodalConductor.coordinates K :=
  NodalAffinePresentation.coordinateEquiv K

theorem zChartEquiv_x :
    zChartEquiv K (xZ K) = NodalAffinePresentation.nodeX K :=
  (NodalAffinePresentation.parameter_base K Polynomial.X).trans (Polynomial.aeval_X _)

theorem zChartEquiv_y :
    zChartEquiv K (yZ K) = NodalAwayNormalization.nodeY K :=
  NodalAffinePresentation.parameter_root K

private theorem yEquation_eq : yEquation K = NodalYChartImmersion.yEquation K :=
  (NodalYChartImmersion.yEquation_printed K).symm

def yChartEquiv : yChart K ≃ₐ[K] yCoordinateRing K :=
  AdjoinRoot.algEquivOfEq K _ _ (yEquation_eq K)

theorem yChartEquiv_x : yChartEquiv K (xY K) = xCoeff K := by
  rw [xY, yChartEquiv, AdjoinRoot.coe_algEquivOfEq, AdjoinRoot.coe_algHomOfDvd,
    AdjoinRoot.liftAlgHom_of] <;> rfl

theorem yChartEquiv_z : yChartEquiv K (zY K) = zCoeff K :=
  AdjoinRoot.algEquivOfEq_root K _ _ (yEquation_eq K)

def zSchemeIso : zScheme K ≅ Spec (CommRingCat.of (NodalConductor.coordinates K)) :=
  Scheme.Spec.mapIso (zChartEquiv K).symm.toCommRingCatIso.op

def ySchemeIso : yScheme K ≅ nodeYChart K :=
  Scheme.Spec.mapIso (yChartEquiv K).symm.toCommRingCatIso.op


end
end ManuscriptAudit.NodalGluedFieldCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalGluedFieldCharts.zChartEquiv,
      ``ManuscriptAudit.NodalGluedFieldCharts.yChartEquiv,
      ``ManuscriptAudit.NodalGluedFieldCharts.zSchemeIso,
      ``ManuscriptAudit.NodalGluedFieldCharts.ySchemeIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
