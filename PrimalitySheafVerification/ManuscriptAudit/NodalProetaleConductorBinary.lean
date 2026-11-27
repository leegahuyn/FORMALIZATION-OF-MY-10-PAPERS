import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeAffineMap
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothRationalBoundary
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapConductorUnit
import PrimalitySheafVerification.ManuscriptAudit.NormalizationBranchChartTransport
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBranchDifferenceEpi

/-! The certified affine crossed cover gives a native binary separator
on the original proper normalization pullback. -/

namespace ManuscriptAudit.NodalProetaleConductorBinary

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (projectiveNode affineOpen)
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalNormalizedNativeCharts (zToNormalized)
open NodalNormalizedNativeAffineMap (zToNormalized_affine_isPullback)
open NodalSmoothRationalBoundary (projectiveOrigin)
open NodalNormalizationFiber (affineNormalization)
open NodalNormalizationBranches (branchMap plus_over_node minus_over_node)
open NodalAffineOrigin (originMap)
open NodalSwapCoverNoSection (coverMap coverScheme coverMap_etale)
open ProetaleContinuousDirectImageMaps
open ProetaleBranchBinaryLabelling (Binary binaryDifference)
open ProetaleBranchDifferenceEpi (oneSection)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance binaryTopology : TopologicalSpace Binary := ⊥
local instance binaryDiscrete : DiscreteTopology Binary := ⟨rfl⟩

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

private abbrev L := Spec (CommRingCat.of (Polynomial K))
private abbrev X := projectiveNode K
private abbrev m := normalizationMap K
private abbrev j := affineOpen K
private abbrev i := originMap K
private abbrev e := zToNormalized K h2
private abbrev n := affineNormalization K
private abbrev a := coverMap K
private abbrev hn := zToNormalized_affine_isPullback K h2

/-- The ordered branches inside the actual proper normalization. -/
abbrev plus : Spec (CommRingCat.of K) ⟶ normalizedNode K := branchMap K 1 ≫ e K h2

abbrev minus : Spec (CommRingCat.of K) ⟶ normalizedNode K := branchMap K (-1) ≫ e K h2

theorem plus_over : plus K h2 ≫ m K = projectiveOrigin K :=
  NormalizationBranchChartTransport.branch_over (j K) (n K) (e K h2) (m K) (hn K h2)
    (i K) (branchMap K 1) (plus_over_node K)

theorem minus_over : minus K h2 ≫ m K = projectiveOrigin K :=
  NormalizationBranchChartTransport.branch_over (j K) (n K) (e K h2) (m K) (hn K h2)
    (i K) (branchMap K (-1)) (minus_over_node K)

include h2 in
abbrev swapObject : (X K).ProEt := by
  letI := coverMap_etale K h2
  exact Scheme.ProEt.mk (a K ≫ j K)

private abbrev normIso :=
  NormalizationBranchChartTransport.normIso (a K) (j K) (n K) (e K h2) (m K) (hn K h2)

private abbrev conductorIso :=
  NormalizationBranchChartTransport.conductorIso (a K) (j K) (i K)

private theorem transport_on_branch (b : Spec (CommRingCat.of K) ⟶ L K)
    (hb : b ≫ n K = i K) (c : ↥(pullback (a K ≫ j K) (projectiveOrigin K) : Scheme.{0})) :
    (normIso K h2).inv
      (pullbackMap (a K ≫ j K) (b ≫ e K h2)
        (NormalizationBranchChartTransport.branch_over (j K) (n K) (e K h2) (m K)
          (hn K h2) (i K) b hb) c) =
        pullbackMap (a K) b hb ((conductorIso K).inv c) := by
  let c' := (conductorIso K).inv c
  have hc : (conductorIso K).hom c' = c :=
    congrArg (fun f : pullback (a K ≫ j K) (projectiveOrigin K) ⟶ pullback (a K ≫ j K) (projectiveOrigin K) ↦ f c)
      (conductorIso K).inv_hom_id
  have h := NormalizationBranchChartTransport.branchIso_natural (a K) (j K) (n K)
    (e K h2) (m K) (hn K h2) (i K) b hb
  have hp := congrArg (fun f : pullback (a K) (i K) ⟶ pullback (a K ≫ j K) (m K) ↦ f c') h
  change pullbackMap (a K ≫ j K) (b ≫ e K h2) _ ((conductorIso K).hom c') =
    (normIso K h2).hom (pullbackMap (a K) b hb c') at hp
  rw [hc] at hp
  rw [hp]
  exact congrArg (fun f : pullback (a K) (n K) ⟶ pullback (a K) (n K) ↦ f (pullbackMap (a K) b hb c'))
    (normIso K h2).hom_inv_id

/-- An actual binary separator on the ambient pullback of the certified swap cover. -/
def separator :
    (functionsOver Binary (m K)).obj.obj (op (swapObject K h2)) :=
  let t : C(↥(pullback (a K) (n K) : Scheme.{0}), Binary) := NodalSwapConductorUnit.unitLift K h2
  ⟨t.comp ⟨(normIso K h2).inv, (normIso K h2).inv.continuous⟩⟩

/-- Its ordered branch difference is the actual constant label 1. -/
theorem separator_difference :
    (binaryDifference (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2)).hom.app
      (op (swapObject K h2)) (separator K h2) =
        oneSection (q := projectiveOrigin K) (swapObject K h2) := by
  apply ULift.ext
  apply ContinuousMap.ext
  intro c
  change ↥(pullback (a K ≫ j K) (projectiveOrigin K) : Scheme.{0}) at c
  let t : C(↥(pullback (a K) (n K) : Scheme.{0}), Binary) := NodalSwapConductorUnit.unitLift K h2
  change t ((normIso K h2).inv (pullbackMap (a K ≫ j K) (plus K h2) (plus_over K h2) c)) -
    t ((normIso K h2).inv (pullbackMap (a K ≫ j K) (minus K h2) (minus_over K h2) c)) = 1
  have hPlus :
      t ((normIso K h2).inv (pullbackMap (a K ≫ j K) (plus K h2) (plus_over K h2) c)) =
        t (pullbackMap (a K) (branchMap K 1) (plus_over_node K) ((conductorIso K).inv c)) :=
    congrArg (fun x : ↥(pullback (a K) (n K) : Scheme.{0}) ↦ t x)
      (transport_on_branch K h2 (branchMap K 1) (plus_over_node K) c)
  have hMinus :
      t ((normIso K h2).inv (pullbackMap (a K ≫ j K) (minus K h2) (minus_over K h2) c)) =
        t (pullbackMap (a K) (branchMap K (-1)) (minus_over_node K) ((conductorIso K).inv c)) :=
    congrArg (fun x : ↥(pullback (a K) (n K) : Scheme.{0}) ↦ t x)
      (transport_on_branch K h2 (branchMap K (-1)) (minus_over_node K) c)
  rw [hPlus, hMinus]
  exact congrArg (fun s : C(↥(pullback (a K) (i K) : Scheme.{0}), Binary) ↦ s ((conductorIso K).inv c))
    (NodalSwapConductorUnit.unitLift_difference K h2)

end
end ManuscriptAudit.NodalProetaleConductorBinary

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProetaleConductorBinary.separator_difference
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
