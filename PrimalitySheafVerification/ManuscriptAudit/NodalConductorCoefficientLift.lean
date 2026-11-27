import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapConductorUnit

/-! A continuous binary separator of the two branches can be relabeled
by an arbitrary discrete abelian group after fixing the positive label. -/

namespace ManuscriptAudit.NodalConductorCoefficientLift

open AlgebraicGeometry CategoryTheory Opposite
open EtaleContinuousDirectImageMaps NodalConductorSheafKernel
open NodalNormalizationEtaleFibers (Norm Conductor plus minus)
open NodalNormalizationFiber (affineNode affineNormalization)
open NodalNormalizationBranches (branchMap plus_over_node)
open NodalSwapCoverNoSection (coverObject)
open NodalSwapConductorUnit (unitLift unitLift_difference)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

abbrev Binary := AddCommGrpCat.of (ZMod 2)
local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

variable (K : Type) [Field K]

/-- The literal positive branch evaluation of the binary section. -/
abbrev positiveTrace : normalizationFunctions K Binary ⟶ conductorFunctions K Binary :=
  restriction Binary (branchMap K 1) (plus_over_node K)

/-- The lifted binary separator also separates branches on each refinement. -/
theorem unitLift_difference_after (h2 : (2 : K) ≠ 0) (U : (affineNode K).Etale)
    (a : U ⟶ coverObject K h2) :
    (branchDifference K Binary).hom.app (op U)
        ((normalizationFunctions K Binary).obj.map a.op (unitLift K h2)) =
      ContinuousMap.const (Conductor K U).left (1 : Binary) := by
  have h := ConcreteCategory.congr_hom
    ((branchDifference K Binary).hom.naturality a.op) (unitLift K h2)
  change (branchDifference K Binary).hom.app (op U)
      ((normalizationFunctions K Binary).obj.map a.op (unitLift K h2)) =
    (conductorFunctions K Binary).obj.map a.op
      ((branchDifference K Binary).hom.app (op (coverObject K h2)) (unitLift K h2)) at h
  rw [unitLift_difference] at h
  exact h

variable (M : AddCommGrpCat.{0}) [TopologicalSpace M] [DiscreteTopology M]
variable [IsTopologicalAddGroup M]

/-- Send one chosen label to the required section value and the other to zero. -/
def relabel (U : (affineNode K).Etale) (ε : Binary) (m : M)
    (b : (normalizationFunctions K Binary).obj.obj (op U)) :
    (normalizationFunctions K M).obj.obj (op U) := by
  classical
  let a : ContinuousMap Binary M := ⟨fun t ↦ if t = ε then m else 0, continuous_of_discreteTopology⟩
  exact a.comp (show ContinuousMap (Norm K U).left Binary from b)

/-- An oriented relabeling has exactly the prescribed difference on the conductor. -/
theorem relabel_difference_const (U : (affineNode K).Etale) (ε : Binary) (m : M)
    (b : (normalizationFunctions K Binary).obj.obj (op U))
    (hDiff : (branchDifference K Binary).hom.app (op U) b =
      ContinuousMap.const (Conductor K U).left (1 : Binary))
    (hPos : (positiveTrace K).hom.app (op U) b = ContinuousMap.const (Conductor K U).left ε) :
    (branchDifference K M).hom.app (op U) (relabel K M U ε m b) =
      ContinuousMap.const (Conductor K U).left m := by
  classical
  apply ContinuousMap.ext
  intro x
  let b' : ContinuousMap (Norm K U).left Binary := b
  have hp : b' (plus K U x) = ε :=
    congrArg (fun s : ContinuousMap (Conductor K U).left Binary ↦ s x) hPos
  have hd : b' (plus K U x) - b' (minus K U x) = 1 :=
    congrArg (fun s : ContinuousMap (Conductor K U).left Binary ↦ s x) hDiff
  have hm : b' (minus K U x) ≠ ε := by
    intro hn
    rw [hp, hn, sub_self] at hd
    exact zero_ne_one hd
  change (if b' (plus K U x) = ε then m else 0) -
    (if b' (minus K U x) = ε then m else 0) = m
  rw [if_pos hp, if_neg hm, sub_zero]

end

end ManuscriptAudit.NodalConductorCoefficientLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalConductorCoefficientLift.unitLift_difference_after,
      ``ManuscriptAudit.NodalConductorCoefficientLift.relabel_difference_const] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
