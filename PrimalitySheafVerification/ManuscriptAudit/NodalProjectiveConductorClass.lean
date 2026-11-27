import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisOrdinary
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveConductorLabels

/-! The native conductor sequence produces a nonzero proper nodal H¹ class. -/

namespace ManuscriptAudit.NodalProjectiveConductorClass

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalNormalizationFiber (affineNode)
open NodalProjectiveClosure (projectiveNode affineOpen)
open NodalProperYChart (chartOpen)
open NodalConductorAbelianSequence (sequence sequence_shortExact)
open NodalProjectiveConductorLabels
open EtaleMayerVietoris (existsHOne_first_not_second_of_local_section_lift terminalCohomologyIso)
open EtaleTwoOpenHOne (identityObject openArrow)
open EtaleContinuousMapSheaf OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]
variable (M : AddCommGrpCat.{0}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev F := (constantSheaf (projectiveNode K).smallEtaleTopology AddCommGrpCat.{0}).obj M

/-- A nonzero conductor label yields a class nonzero on the affine chart and zero on the Y chart. -/
theorem exists_class_affine_nonzero_chart_zero (h2 : (2 : K) ≠ 0) (m : M) (hm : m ≠ 0) :
    ∃ z : (F K M).H' 1 (identityObject (projectiveNode K)),
      ((F K M).cohomologyPresheaf 1).map (openArrow (affineOpen K)).op z ≠ 0 ∧
      ((F K M).cohomologyPresheaf 1).map (openArrow (chartOpen K)).op z = 0 := by
  let j := affineOpen K
  let k := chartOpen K
  let e : (sequence K M).X₁ ≅ (restriction j AddCommGrpCat.{0}).obj (F K M) :=
    (constantSheafContinuousMapIso (affineNode K) M).symm ≪≫ ((restrictionConstantIso j).app M).symm
  have hCover : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun W : (projectiveNode K).Opens ↦ (W : Set (projectiveNode K)))
      (NodalChartIntersection.charts_cover K)
  exact existsHOne_first_not_second_of_local_section_lift j k hCover (F K M) (sequence K M)
    (sequence_shortExact K M h2) e (conductorLabel K M m)
    (conductorLabel_unliftable K M m hm) (conductorLabel_lift_on_overlap K M m)

/-- The actual ordinary proper nodal H¹ is nontrivial for every nonzero conductor label. -/
theorem projectiveHOne_nontrivial (h2 : (2 : K) ≠ 0) (m : M) (hm : m ≠ 0) :
    Nontrivial (Sheaf.H (F K M) 1) := by
  obtain ⟨z, hz, _⟩ := exists_class_affine_nonzero_chart_zero K M h2 m hm
  let e := (terminalCohomologyIso (F K M) 1).addCommGroupIsoToAddEquiv
  refine ⟨⟨e z, e 0, fun h ↦ hz ?_⟩⟩
  rw [e.injective h, map_zero]

end
end ManuscriptAudit.NodalProjectiveConductorClass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveConductorClass.exists_class_affine_nonzero_chart_zero,
      ``ManuscriptAudit.NodalProjectiveConductorClass.projectiveHOne_nontrivial] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
