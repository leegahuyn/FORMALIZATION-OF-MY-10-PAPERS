import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleConstantHZeroRestriction
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisLocalBoundary
import PrimalitySheafVerification.ManuscriptAudit.MayerVietorisPairInjective
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveConductorLabels
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartPrincipalOpen

/-! Every conductor label gives an additive and uniquely specified
degree-one class on the actual proper nodal curve. -/

namespace ManuscriptAudit.NodalProjectiveConductorAdditive

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (projectiveNode affineOpen affineNode)
open NodalProperYChart (chartOpen)
open NodalConductorAbelianSequence (sequence sequence_shortExact)
open NodalProjectiveConductorLabels
open EtaleMayerVietoris EtaleMayerVietorisLocalBoundary
open EtaleTwoOpenHOne (identityObject openArrow)
open EtaleOpenIntersection (fstLeg sndLeg intersection_isPullback)
open EtaleContinuousMapSheaf OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]
variable (M : AddCommGrpCat.{0}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev j := affineOpen K
private abbrev k := chartOpen K
private abbrev F := (constantSheaf (projectiveNode K).smallEtaleTopology AddCommGrpCat.{0}).obj M
private abbrev terminal := identityObject (projectiveNode K)

private theorem charts_cover : Set.range (j K) ∪ Set.range (k K) = Set.univ :=
  congrArg (fun W : (projectiveNode K).Opens ↦ (W : Set (projectiveNode K)))
    (NodalChartIntersection.charts_cover K)

private def kernelIso :
    (sequence K M).X₁ ≅ (restriction (j K) AddCommGrpCat.{0}).obj (F K M) :=
  (constantSheafContinuousMapIso (affineNode K) M).symm ≪≫
    ((restrictionConstantIso (j K)).app M).symm

private def labels :
    M →+ (sequence K M).X₃.obj.obj (op (identityObject (affineNode K))) where
  toFun := conductorLabel K M
  map_zero' := by
    change ContinuousMap.const _ (0 : M) = (0 : ContinuousMap _ M)
    exact ContinuousMap.ext fun _ ↦ rfl
  map_add' a b := by
    change ContinuousMap.const _ (a + b) = ContinuousMap.const _ a + ContinuousMap.const _ b
    exact ContinuousMap.ext fun _ ↦ rfl

private def affineClass (h2 : (2 : K) ≠ 0) :
    M →+ (F K M).H' 1 (Scheme.Etale.mk (j K)) :=
  (localBoundaryMap (j K) (F K M) (sequence K M) (sequence_shortExact K M h2)
    (kernelIso K M)).comp (labels K M)

private theorem affineClass_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (affineClass K M h2) := by
  intro a b hab
  apply sub_eq_zero.mp
  by_contra h
  have hz : affineClass K M h2 (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hl := (localBoundaryMap_zero_iff (j K) (F K M) (sequence K M)
    (sequence_shortExact K M h2) (kernelIso K M) (conductorLabel K M (a - b))).mp hz
  exact conductorLabel_unliftable K M (a - b) h hl

private abbrev first :=
  ((F K M).cohomologyPresheaf 1).map (openArrow (j K)).op

private abbrev second :=
  ((F K M).cohomologyPresheaf 1).map (openArrow (k K)).op

private theorem pair_injective :
    Function.Injective (fun z : (F K M).H' 1 (terminal K) ↦
      (first K M z, second K M z)) := by
  let l := pullback.fst (j K) (k K) ≫ j K
  let S := openCoverSquare (j K) (k K) l (fstLeg (j K) (k K)) (sndLeg (j K) (k K))
    (intersection_isPullback (j K) (k K)) (charts_cover K)
  letI : PreconnectedSpace (NodalYChartPrincipalOpen.overlapObject K).left :=
    NodalYChartPrincipalOpen.overlap_preconnected K
  letI : Nonempty (NodalYChartPrincipalOpen.overlapObject K).left :=
    NodalYChartPrincipalOpen.overlap_nonempty K
  have hLower : Function.Surjective
    (((F K M).cohomologyPresheaf 0).map (fstLeg (j K) (k K)).op) :=
    EtaleConstantHZeroRestriction.restriction_surjective M (fstLeg (j K) (k K))
  exact MayerVietorisPairInjective.pair_injective S (F K M) 0 hLower

private theorem exists_ambient (h2 : (2 : K) ≠ 0) (m : M) :
    ∃ z : (F K M).H' 1 (terminal K),
      first K M z = affineClass K M h2 m ∧ second K M z = 0 := by
  apply existsHOne_of_compatible_pair (j K) (k K) (F K M) (charts_cover K)
  rw [map_zero]
  exact localBoundaryMap_overlap_zero (j K) (k K) (F K M) (sequence K M)
    (sequence_shortExact K M h2) (kernelIso K M) (conductorLabel K M m)
    (conductorLabel_lift_on_overlap K M m)

private def ambient (h2 : (2 : K) ≠ 0) (m : M) : (F K M).H' 1 (terminal K) :=
  (exists_ambient K M h2 m).choose

private theorem first_ambient (h2 : (2 : K) ≠ 0) (m : M) :
    first K M (ambient K M h2 m) = affineClass K M h2 m :=
  (exists_ambient K M h2 m).choose_spec.1

private theorem second_ambient (h2 : (2 : K) ≠ 0) (m : M) :
    second K M (ambient K M h2 m) = 0 :=
  (exists_ambient K M h2 m).choose_spec.2

private def ambientAddHom (h2 : (2 : K) ≠ 0) : M →+ (F K M).H' 1 (terminal K) where
  toFun := ambient K M h2
  map_zero' := by
    apply pair_injective K M
    exact Prod.ext (by simp only [first_ambient, map_zero])
      (by simp only [second_ambient, map_zero])
  map_add' a b := by
    apply pair_injective K M
    exact Prod.ext (by simp only [first_ambient, map_add])
      (by simp only [second_ambient, map_add, add_zero])

/-- An actual conductor label maps additively to the corresponding
ordinary proper nodal cohomology class. -/
def conductorMap (h2 : (2 : K) ≠ 0) : M →+ Sheaf.H (F K M) 1 :=
  (terminalCohomologyIso (F K M) 1).addCommGroupIsoToAddEquiv.toAddMonoidHom.comp
    (ambientAddHom K M h2)

/-- The actual proper cohomology class determines the conductor label. -/
theorem conductorMap_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (conductorMap K M h2) := by
  let e := (terminalCohomologyIso (F K M) 1).addCommGroupIsoToAddEquiv
  intro a b hab
  have h : ambient K M h2 a = ambient K M h2 b := e.injective hab
  apply affineClass_injective K M h2
  rw [← first_ambient K M h2 a, ← first_ambient K M h2 b, h]

end
end ManuscriptAudit.NodalProjectiveConductorAdditive

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveConductorAdditive.conductorMap,
      ``ManuscriptAudit.NodalProjectiveConductorAdditive.conductorMap_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
