import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisLocalSection
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorAbelianSequence
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveOverlapConductorEmpty

/-! A nonzero constant conductor label lifts on the overlap and fails to lift globally. -/

namespace ManuscriptAudit.NodalProjectiveConductorLabels

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalNormalizationFiber (affineNode)
open NodalAffineOrigin (originMap)
open NodalNormalizationEtaleFibers (Conductor)
open NodalConductorAbelianSequence (sequence)
open NodalConductorAbelianHZero (terminal_branch_difference_zero)
open NodalProjectiveOverlapConductorEmpty
open EtaleMayerVietoris (SectionHasLift)
open EtaleTwoOpenHOne (identityObject openArrow)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 350000

variable (K : Type) [Field K]
variable (M : AddCommGrpCat.{0}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

abbrev terminal := identityObject (affineNode K)

def conductorLabel (m : M) : (sequence K M).X₃.obj.obj (op (terminal K)) :=
  ContinuousMap.const (Conductor K (terminal K)).left m

theorem conductorLabel_unliftable (m : M) (hm : m ≠ 0) :
    ¬ SectionHasLift (sequence K M) (terminal K) (conductorLabel K M m) := by
  rintro ⟨x, hx⟩
  have hZero : (sequence K M).g.hom.app (op (terminal K)) x = 0 :=
    terminal_branch_difference_zero K M x
  have he : conductorLabel K M m = 0 := hx.symm.trans hZero
  let r : (Conductor K (terminal K)).left ≅ Spec (CommRingCat.of K) :=
    asIso (pullback.snd (𝟙 (affineNode K)) (originMap K))
  let q := r.inv (IsLocalRing.closedPoint K)
  exact hm (congrArg (fun s : ContinuousMap (Conductor K (terminal K)).left M ↦ s q) he)

theorem conductorLabel_lift_on_overlap (m : M) :
    SectionHasLift (sequence K M) (overlap K)
      ((sequence K M).X₃.obj.map (openArrow (overlapMap K)).op (conductorLabel K M m)) := by
  have hEmpty : IsEmpty (Conductor K (overlap K)).left := by
    change IsEmpty (pullback (overlapMap K) (originMap K) : Scheme.{0})
    exact overlap_conductor_isEmpty K
  have hUnique : Subsingleton (ContinuousMap (Conductor K (overlap K)).left M) :=
    ⟨fun f g ↦ ContinuousMap.ext fun x ↦ (hEmpty.false x).elim⟩
  exact ⟨0, hUnique.elim _ _⟩

end
end ManuscriptAudit.NodalProjectiveConductorLabels

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveConductorLabels.conductorLabel_unliftable,
      ``ManuscriptAudit.NodalProjectiveConductorLabels.conductorLabel_lift_on_overlap] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
