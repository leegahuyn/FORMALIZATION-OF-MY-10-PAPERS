import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorSheafKernel
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapBranchIdempotent
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverNoSection

/-! On the actual crossed étale cover, the bright and dark normalization
components give a section whose two branch values differ by one mod two. -/

namespace ManuscriptAudit.NodalSwapConductorUnit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Polynomial
open NodalSwapCover (Cover)
open NodalSwapCoverNoSection (coverObject coverMap)
open NodalSwapBranchIdempotent (A B E t z skew idempotent idempotent_mul
  positive_branch_label negative_branch_label)
open NodalNormalizationFiber (affineNormalization)
open NodalNormalizationBranches (branchMap branchPoint plus_over_node minus_over_node)
open NodalNormalizationEtaleFibers (Norm Conductor plus minus)
open NodalConductorSheafKernel (branchDifference normalizationFunctions conductorFunctions)
open NodalAffineOrigin (originMap)
open EtaleContinuousDirectImageMaps (baseChangeMap_fst baseChangeMap_snd)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

private abbrev T := coverObject K h2
private abbrev C := AddCommGrpCat.of (ZMod 2)

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

private def tensorToCover : Spec (CommRingCat.of (E K)) ⟶ (T K h2).left :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight : Cover K →ₐ[A K] E K).toRingHom))

private def tensorToLine : Spec (CommRingCat.of (E K)) ⟶ NodalNormalizationFiber.affineLine K :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeLeft : B K →ₐ[A K] E K).toRingHom))

private theorem tensor_pullback :
    IsPullback (tensorToCover K h2) (tensorToLine K) (T K h2).hom (affineNormalization K) := by
  apply IsPullback.flip
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    ⟨⟨(CommRingCat.pushoutCocone (A K) (B K) (Cover K)).condition⟩,
      ⟨CommRingCat.pushoutCoconeIsColimit (A K) (B K) (Cover K)⟩⟩

private def normIso : Spec (CommRingCat.of (E K)) ≅ (Norm K (T K h2)).left :=
  (tensor_pullback K h2).isoPullback

private theorem coordinate_plus_eval (c : (Conductor K (T K h2)).left) :
    tensorToLine K ((normIso K h2).inv (plus K (T K h2) c)) = branchPoint K 1 := by
  change ((normIso K h2).inv ≫ tensorToLine K) (plus K (T K h2) c) = _
  rw [(tensor_pullback K h2).isoPullback_inv_snd]
  change (plus K (T K h2) ≫ pullback.snd (T K h2).hom (affineNormalization K)) c = _
  unfold plus
  rw [baseChangeMap_snd]
  change branchMap K 1 (pullback.snd (T K h2).hom (originMap K) c) =
    branchMap K 1 (IsLocalRing.closedPoint K)
  exact congrArg (branchMap K 1) (Subsingleton.elim _ _)

private theorem coordinate_minus_eval (c : (Conductor K (T K h2)).left) :
    tensorToLine K ((normIso K h2).inv (minus K (T K h2) c)) = branchPoint K (-1) := by
  change ((normIso K h2).inv ≫ tensorToLine K) (minus K (T K h2) c) = _
  rw [(tensor_pullback K h2).isoPullback_inv_snd]
  change (minus K (T K h2) ≫ pullback.snd (T K h2).hom (affineNormalization K)) c = _
  unfold minus
  rw [baseChangeMap_snd]
  change branchMap K (-1) (pullback.snd (T K h2).hom (originMap K) c) =
    branchMap K (-1) (IsLocalRing.closedPoint K)
  exact congrArg (branchMap K (-1)) (Subsingleton.elim _ _)

private theorem same_cover_coordinate (c : (Conductor K (T K h2)).left) :
    tensorToCover K h2 ((normIso K h2).inv (plus K (T K h2) c)) =
      tensorToCover K h2 ((normIso K h2).inv (minus K (T K h2) c)) := by
  change ((normIso K h2).inv ≫ tensorToCover K h2) (plus K (T K h2) c) =
    ((normIso K h2).inv ≫ tensorToCover K h2) (minus K (T K h2) c)
  rw [(tensor_pullback K h2).isoPullback_inv_fst]
  change (plus K (T K h2) ≫ pullback.fst (T K h2).hom (affineNormalization K)) c =
    (minus K (T K h2) ≫ pullback.fst (T K h2).hom (affineNormalization K)) c
  unfold plus minus
  rw [baseChangeMap_fst, baseChangeMap_fst]

private theorem branch_asIdeal (a : K) :
    (branchPoint K a).asIdeal = RingHom.ker (Polynomial.evalRingHom a) := by
  unfold branchPoint branchMap
  rw [Spec.map_apply, show IsLocalRing.closedPoint K = (⊥ : PrimeSpectrum K) from Subsingleton.elim _ _]
  rfl

private theorem at_positive (c : (Conductor K (T K h2)).left) :
    t K - 1 ∈ ((normIso K h2).inv (plus K (T K h2) c)).asIdeal := by
  change Polynomial.X - 1 ∈
    (tensorToLine K ((normIso K h2).inv (plus K (T K h2) c))).asIdeal
  rw [coordinate_plus_eval, branch_asIdeal]
  exact RingHom.mem_ker.mpr (by simp)

private theorem at_negative (c : (Conductor K (T K h2)).left) :
    t K + 1 ∈ ((normIso K h2).inv (minus K (T K h2) c)).asIdeal := by
  change Polynomial.X + 1 ∈
    (tensorToLine K ((normIso K h2).inv (minus K (T K h2) c))).asIdeal
  rw [coordinate_minus_eval, branch_asIdeal]
  exact RingHom.mem_ker.mpr (by simp)

private theorem opposite_labels (c : (Conductor K (T K h2)).left) :
    idempotent K h2 ∉ ((normIso K h2).inv (plus K (T K h2) c)).asIdeal ↔
      idempotent K h2 ∈ ((normIso K h2).inv (minus K (T K h2) c)).asIdeal := by
  rw [← positive_branch_label K h2 _ (at_positive K h2 c),
    ← negative_branch_label K h2 _ (at_negative K h2 c)]
  change (skew K - 1) ∈ (tensorToCover K h2 ((normIso K h2).inv
      (plus K (T K h2) c))).asIdeal ↔
    (skew K - 1) ∈ (tensorToCover K h2 ((normIso K h2).inv
      (minus K (T K h2) c))).asIdeal
  rw [same_cover_coordinate]

private def indicator : ContinuousMap (PrimeSpectrum (E K)) C := by
  classical
  let e := idempotent K h2
  let U : Set (PrimeSpectrum (E K)) := PrimeSpectrum.basicOpen e
  have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, idempotent_mul K h2, sub_self]
  have hadd : e + (1 - e) = 1 := by ring
  have hU : IsClopen U := PrimeSpectrum.isClopen_basicOpen_of_mul_add e (1 - e) hmul hadd
  exact ⟨U.piecewise (fun _ => 1) (fun _ => 0),
    continuous_const.piecewise (by simp [hU.frontier_eq]) continuous_const⟩

/-- A literal function on the normalized crossed cover whose two branch
values have difference 1 at every conductor lift. -/
def unitLift : (normalizationFunctions K C).obj.obj (op (T K h2)) :=
  (indicator K h2).comp ⟨(normIso K h2).inv, (normIso K h2).inv.continuous⟩

theorem unitLift_difference :
    (branchDifference K C).hom.app (op (T K h2)) (unitLift K h2) =
      ContinuousMap.const (Conductor K (T K h2)).left (1 : C) := by
  classical
  apply ContinuousMap.ext
  intro c
  change (indicator K h2) ((normIso K h2).inv (plus K (T K h2) c)) -
    (indicator K h2) ((normIso K h2).inv (minus K (T K h2) c)) = 1
  have h := opposite_labels K h2 c
  by_cases hpos : idempotent K h2 ∉ ((normIso K h2).inv (plus K (T K h2) c)).asIdeal
  · have hneg := h.mp hpos
    simp [indicator, Set.piecewise, PrimeSpectrum.mem_basicOpen, hpos, hneg]
  · have hneg := fun hm => hpos (h.mpr hm)
    simp [indicator, Set.piecewise, PrimeSpectrum.mem_basicOpen, hpos, hneg] <;> decide

end
end ManuscriptAudit.NodalSwapConductorUnit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalSwapConductorUnit.unitLift_difference
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
