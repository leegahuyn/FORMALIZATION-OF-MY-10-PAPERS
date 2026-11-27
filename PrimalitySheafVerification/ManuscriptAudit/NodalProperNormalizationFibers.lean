import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SchemePullbackChartPoints
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineBranchPairs
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedMapSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleConductorBinary

/-! The actual ordered proper nodal branches describe every distinct
pair in a base-changed normalization fiber. -/

namespace ManuscriptAudit.NodalProperNormalizationFibers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemePullbackChartPoints
open ProetaleContinuousDirectImageMaps (pullbackMap)
open ProetaleTwoBranchKernel (BranchFibers)
open NodalProjectiveClosure (projectiveNode affineOpen)
open NodalProjectiveNormalization (normalizationMap)
open NodalProperYChart (chartOpen)
open NodalYChartImmersion (nodeYChart)
open NodalNormalizedNativeCharts
open NodalNormalizedNativeAffineMap
open NodalNormalizedMapSurjectivity (chartRanges)
open NodalNormalizationFiber (affineNode affineNormalization)
open NodalNormalizationBranches (branchMap plus_over_node minus_over_node)
open NodalAffineOrigin (originMap)
open NodalSmoothRationalBoundary (projectiveOrigin)
open NodalProetaleConductorBinary (plus minus plus_over minus_over)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev X := projectiveNode K
private abbrev p := normalizationMap K
private abbrev j := affineOpen K
private abbrev n := affineNormalization K

variable {W : Scheme.{0}} (a : W ⟶ X K)

private theorem points_equal_over_Y
    (s t : ↥(pullback a (p K) : Scheme.{0})) (w : W) (y : nodeYChart K)
    (hy : a w = chartOpen K y)
    (hs : pullback.fst a (p K) s = w) (ht : pullback.fst a (p K) t = w) : s = t := by
  let m := pullback.fst a (chartOpen K)
  let b := pullback.snd a (chartOpen K)
  let hc : b ≫ chartOpen K = m ≫ a := pullback.condition.symm
  let H := yToNormalized_isPullback K
  let l := fromChart m b a (chartOpen K) hc (𝟙 _) (yToNormalized K) (p K) H.w
  let hL : IsPullback l (pullback.fst b (𝟙 _)) (pullback.fst a (p K)) m :=
    fromChart_isPullback m b a (chartOpen K) hc (𝟙 _) (yToNormalized K) (p K) H
  obtain ⟨u, hu, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := chartOpen K) w y hy
  obtain ⟨s', hs', hsu⟩ := points_lift hL s u (hs.trans hu.symm)
  obtain ⟨t', ht', htu⟩ := points_lift hL t u (ht.trans hu.symm)
  have hEq : s' = t' := (pullback.fst b (𝟙 _)).homeomorph.injective
    (by simpa only [Scheme.Hom.homeomorph_apply] using hsu.trans htu.symm)
  exact hs'.symm.trans ((congrArg l hEq).trans ht')

variable (h2 : (2 : K) ≠ 0)

private abbrev e := zToNormalized K h2
private abbrev liftPlus := pullbackMap a (plus K h2) (plus_over K h2)
private abbrev liftMinus := pullbackMap a (minus K h2) (minus_over K h2)

private theorem pair_over_Z
    (s t : ↥(pullback a (p K) : Scheme.{0})) (w : W) (z : affineNode K) (hz : a w = j K z)
    (hs : pullback.fst a (p K) s = w) (ht : pullback.fst a (p K) t = w) :
    s = t ∨ ∃ c : ↥(pullback a (projectiveOrigin K) : Scheme.{0}),
      (liftPlus K a h2 c = s ∧ liftMinus K a h2 c = t) ∨
      (liftPlus K a h2 c = t ∧ liftMinus K a h2 c = s) := by
  let m := pullback.fst a (j K)
  let b := pullback.snd a (j K)
  let hc : b ≫ j K = m ≫ a := pullback.condition.symm
  let H := zToNormalized_affine_isPullback K h2
  let l := fromChart m b a (j K) hc (n K) (e K h2) (p K) H.w
  let hL : IsPullback l (pullback.fst b (n K)) (pullback.fst a (p K)) m :=
    fromChart_isPullback m b a (j K) hc (n K) (e K h2) (p K) H
  let cMap : pullback b (originMap K) ⟶ pullback a (projectiveOrigin K) :=
    fromChart m b a (j K) hc (originMap K) (𝟙 _) (projectiveOrigin K) (Category.id_comp _)
  have hPlus (c : ↥(pullback b (originMap K) : Scheme.{0})) :
      l (NodalAffineNormalizationFibers.plus K b c) = liftPlus K a h2 (cMap c) :=
    congrArg (fun f : pullback b (originMap K) ⟶ pullback a (p K) ↦ f c)
      (fromChart_branch m b a (j K) hc (n K) (e K h2) (p K) H.w
        (originMap K) (branchMap K 1) (plus_over_node K))
  have hMinus (c : ↥(pullback b (originMap K) : Scheme.{0})) :
      l (NodalAffineNormalizationFibers.minus K b c) = liftMinus K a h2 (cMap c) :=
    congrArg (fun f : pullback b (originMap K) ⟶ pullback a (p K) ↦ f c)
      (fromChart_branch m b a (j K) hc (n K) (e K h2) (p K) H.w
        (originMap K) (branchMap K (-1)) (minus_over_node K))
  obtain ⟨u, hu, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := j K) w z hz
  obtain ⟨s', hs', hsu⟩ := points_lift hL s u (hs.trans hu.symm)
  obtain ⟨t', ht', htu⟩ := points_lift hL t u (ht.trans hu.symm)
  rcases NodalAffineBranchPairs.points_eq_or_branchPair K b s' t' (hsu.trans htu.symm) with
    h | ⟨c, h | h⟩
  · exact Or.inl (hs'.symm.trans ((congrArg l h).trans ht'))
  · exact Or.inr ⟨cMap c, Or.inl
      ⟨(hPlus c).symm.trans ((congrArg l h.1).trans hs'),
       (hMinus c).symm.trans ((congrArg l h.2).trans ht')⟩⟩
  · exact Or.inr ⟨cMap c, Or.inr
      ⟨(hPlus c).symm.trans ((congrArg l h.1).trans ht'),
       (hMinus c).symm.trans ((congrArg l h.2).trans hs')⟩⟩

/-- Every actual pro-étale chart sees the ordered geometric branch
pairs of the proper nodal normalization. -/
theorem branchFibers :
    BranchFibers (p K) (projectiveOrigin K) (plus K h2) (minus K h2)
      (plus_over K h2) (minus_over K h2) := by
  intro U s t h
  let w := pullback.fst U.hom (p K) s
  have hw : U.hom w ∈ Set.range (j K) ∪ Set.range (chartOpen K) :=
    (chartRanges K).symm ▸ Set.mem_univ _
  rcases hw with ⟨z, hz⟩ | ⟨y, hy⟩
  · exact pair_over_Z K U.hom h2 s t w z hz.symm rfl h.symm
  · exact Or.inl (points_equal_over_Y K U.hom s t w y hy.symm rfl h.symm)

end
end ManuscriptAudit.NodalProperNormalizationFibers

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProperNormalizationFibers.branchFibers
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
