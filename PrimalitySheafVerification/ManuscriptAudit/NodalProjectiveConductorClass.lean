import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisLocalSection
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianSequence
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocus

/-! The actual ordered conductor sequence produces a nonzero proper
nodal H¹ class for any nonzero discrete coefficient label. -/

namespace ManuscriptAudit.NodalProjectiveConductorClass

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalNormalizationFiber (affineNode)
open NodalProjectiveClosure (projectiveNode affineOpen)
open NodalProperYChart NodalYChartImmersion
open NodalAffineOrigin (originMap originPoint)
open NodalNormalizationEtaleFibers (Conductor)
open NodalConductorAbelianSequence (sequence sequence_shortExact)
open NodalConductorAbelianHZero (terminal_branch_difference_zero)
open NodalConductorSheafKernel (branchDifference)
open NodalSmoothLocus (nodePoint smooth_pieces_cover_complement)
open EtaleMayerVietoris (SectionHasLift HOne_nontrivial_of_local_section_lift)
open EtaleTwoOpenHOne (identityObject openArrow)
open EtaleContinuousMapSheaf OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

private abbrev overlapMap := pullback.fst (affineOpen K) (chartOpen K)
private abbrev overlap := Scheme.Etale.mk (overlapMap K)

private theorem pullback_no_points {S U V : Scheme.{0}} (f : U ⟶ S) (g : V ⟶ S)
    (h : ∀ (x : U) (y : V), f x ≠ g y) : IsEmpty (pullback f g : Scheme.{0}) := by
  refine ⟨fun z ↦ h (pullback.fst f g z) (pullback.snd f g z) ?_⟩
  exact congrArg (fun m : pullback f g ⟶ S ↦ m z) pullback.condition

set_option maxHeartbeats 1000000 in
/-- The actual overlap of the two standard charts has empty conductor pullback. -/
theorem overlap_conductor_isEmpty :
    IsEmpty (pullback (overlapMap K) (originMap K) : Scheme.{0}) := by
  apply pullback_no_points
  intro p q hp
  have hq : q = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hOrigin : overlapMap K p = originPoint K :=
    hp.trans (congrArg (originMap K) hq)
  have hSquare : chartOpen K (pullback.snd (affineOpen K) (chartOpen K) p) =
      affineOpen K (overlapMap K p) :=
    congrArg (fun m : pullback (affineOpen K) (chartOpen K) ⟶ projectiveNode K ↦ m p)
      (pullback.condition (f := affineOpen K) (g := chartOpen K)).symm
  have hChart : nodePoint K ∈ Set.range (chartOpen K) :=
    ⟨_, hSquare.trans (congrArg (affineOpen K) hOrigin)⟩
  have hOut : nodePoint K ∈ ({nodePoint K} : Set (projectiveNode K))ᶜ :=
    (smooth_pieces_cover_complement K).le (Or.inr hChart)
  exact hOut (Set.mem_singleton _)

variable (M : AddCommGrpCat.{0}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev F := (constantSheaf (projectiveNode K).smallEtaleTopology AddCommGrpCat.{0}).obj M
private abbrev terminal := identityObject (affineNode K)

private def conductorLabel (m : M) : (sequence K M).X₃.obj.obj (op (terminal K)) :=
  ContinuousMap.const (Conductor K (terminal K)).left m

private theorem conductorLabel_unliftable (m : M) (hm : m ≠ 0) :
    ¬ SectionHasLift (sequence K M) (terminal K) (conductorLabel K M m) := by
  rintro ⟨x, hx⟩
  have hZero : (sequence K M).g.hom.app (op (terminal K)) x = 0 :=
    terminal_branch_difference_zero K M x
  have he : conductorLabel K M m = 0 := hx.symm.trans hZero
  let r : (Conductor K (terminal K)).left ≅ Spec (CommRingCat.of K) :=
    asIso (pullback.snd (𝟙 (affineNode K)) (originMap K))
  let q := r.inv (IsLocalRing.closedPoint K)
  exact hm (congrArg (fun s : ContinuousMap (Conductor K (terminal K)).left M ↦ s q) he)

private theorem conductorLabel_lift_on_overlap (m : M) :
    SectionHasLift (sequence K M) (overlap K)
      ((sequence K M).X₃.obj.map (openArrow (overlapMap K)).op (conductorLabel K M m)) := by
  let empty := overlap_conductor_isEmpty K
  refine ⟨0, ?_⟩
  change ((sequence K M).g.hom.app (op (overlap K))).hom 0 = _
  rw [map_zero]
  apply ContinuousMap.ext
  intro q
  exact (empty.false (show (pullback (overlapMap K) (originMap K) : Scheme.{0}) from q)).elim

/-- A nonzero label yields an actual nonzero class in ordinary proper
nodal H¹, using compatible local classes on the two real charts. -/
theorem projectiveHOne_nontrivial (h2 : (2 : K) ≠ 0) (m : M) (hm : m ≠ 0) :
    Nontrivial (Sheaf.H (F K M) 1) := by
  let j := affineOpen K
  let k := chartOpen K
  let e : (sequence K M).X₁ ≅ (restriction j AddCommGrpCat.{0}).obj (F K M) :=
    (constantSheafContinuousMapIso (affineNode K) M).symm ≪≫ ((restrictionConstantIso j).app M).symm
  have hCover : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun W : (projectiveNode K).Opens ↦ (W : Set (projectiveNode K)))
      (NodalChartIntersection.charts_cover K)
  exact HOne_nontrivial_of_local_section_lift j k hCover (F K M) (sequence K M)
    (sequence_shortExact K M h2) e (conductorLabel K M m)
    (conductorLabel_unliftable K M m hm) (conductorLabel_lift_on_overlap K M m)

end

end ManuscriptAudit.NodalProjectiveConductorClass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveConductorClass.overlap_conductor_isEmpty,
      ``ManuscriptAudit.NodalProjectiveConductorClass.projectiveHOne_nontrivial] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
