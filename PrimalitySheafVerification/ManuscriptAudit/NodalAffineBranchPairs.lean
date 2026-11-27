import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineNormalizationFibers

/-! The actual ordered pair of branches after arbitrary scheme base
change of the affine normalization. -/

namespace ManuscriptAudit.NodalAffineBranchPairs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (pullbackMap_fst)
open NodalNormalizationFiber (affineNode affineNormalization)
open NodalNormalizationBranches (branchMap plus_over_node minus_over_node)
open NodalAffineOrigin (originMap originPoint)
open NodalAffineNormalizationFibers

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] {W : Scheme.{0}} (a : W ⟶ affineNode K)

private abbrev projection := pullback.fst a (affineNormalization K)
private abbrev conductorProjection := pullback.fst a (originMap K)

private theorem plus_projection (c : Conductor K a) :
    projection K a (plus K a c) = conductorProjection K a c :=
  congrArg (fun f : Conductor K a ⟶ W ↦ f c)
    (pullbackMap_fst a (branchMap K 1) (plus_over_node K))

private theorem minus_projection (c : Conductor K a) :
    projection K a (minus K a c) = conductorProjection K a c :=
  congrArg (fun f : Conductor K a ⟶ W ↦ f c)
    (pullbackMap_fst a (branchMap K (-1)) (minus_over_node K))

/-- Two distinct points with the same projection are the ordered
branch pair, possibly in reverse order, at a common conductor point. -/
theorem points_eq_or_branchPair (s t : Norm K a)
    (hst : projection K a s = projection K a t) :
    s = t ∨ ∃ c : Conductor K a,
      (plus K a c = s ∧ minus K a c = t) ∨
      (plus K a c = t ∧ minus K a c = s) := by
  by_cases h : a (projection K a s) = originPoint K
  · have ht : a (projection K a t) = originPoint K := (congrArg a hst.symm).trans h
    have join {c d : Conductor K a}
        (hc : projection K a s = conductorProjection K a c)
        (hd : projection K a t = conductorProjection K a d) : c = d :=
      conductor_projection_injective K a (hc.symm.trans (hst.trans hd))
    rcases point_lifts_to_branch K a s h with ⟨c, hc⟩ | ⟨c, hc⟩
    · rcases point_lifts_to_branch K a t ht with ⟨d, hd⟩ | ⟨d, hd⟩
      · have e := join ((congrArg (projection K a) hc.symm).trans (plus_projection K a c))
          ((congrArg (projection K a) hd.symm).trans (plus_projection K a d))
        exact Or.inl (hc.symm.trans ((congrArg (plus K a) e).trans hd))
      · have e := join ((congrArg (projection K a) hc.symm).trans (plus_projection K a c))
          ((congrArg (projection K a) hd.symm).trans (minus_projection K a d))
        exact Or.inr ⟨c, Or.inl ⟨hc, (congrArg (minus K a) e).trans hd⟩⟩
    · rcases point_lifts_to_branch K a t ht with ⟨d, hd⟩ | ⟨d, hd⟩
      · have e := join ((congrArg (projection K a) hc.symm).trans (minus_projection K a c))
          ((congrArg (projection K a) hd.symm).trans (plus_projection K a d))
        exact Or.inr ⟨c, Or.inr ⟨(congrArg (plus K a) e).trans hd, hc⟩⟩
      · have e := join ((congrArg (projection K a) hc.symm).trans (minus_projection K a c))
          ((congrArg (projection K a) hd.symm).trans (minus_projection K a d))
        exact Or.inl (hc.symm.trans ((congrArg (minus K a) e).trans hd))
  · exact Or.inl (points_equal_off_conductor K a s t (projection K a s) h rfl hst.symm)

end
end ManuscriptAudit.NodalAffineBranchPairs

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalAffineBranchPairs.points_eq_or_branchPair
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
