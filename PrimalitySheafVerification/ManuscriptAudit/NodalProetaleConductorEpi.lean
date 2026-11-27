import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleConductorBinary
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocus
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift

/-! The actual proper nodal conductor difference is an epimorphism
for every discrete abelian coefficient group. -/

namespace ManuscriptAudit.NodalProetaleConductorEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (projectiveNode affineOpen)
open NodalProjectiveNormalization (normalizationMap)
open NodalProperYChart (chartOpen)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed)
open NodalSwapCoverNoSection (coverMap coverMap_etale coverMap_surjective)
open NodalProetaleConductorBinary
open ProetaleBranchBinaryLabelling (Binary binaryDifference)
open ProetaleBranchDifferenceEpi (oneSection oneSection_restrict)
open ProetaleContinuousDirectImageMaps (functionsOver)
open ProetaleTwoBranchKernel (difference)
open TwoOpenCokernelLift (coverObjects coverArrows)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance binaryTopology : TopologicalSpace Binary := ⊥
local instance binaryDiscrete : DiscreteTopology Binary := ⟨rfl⟩

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

private abbrev X := projectiveNode K
private abbrev Y := Scheme.ProEt.mk (chartOpen K)
private abbrev T := Scheme.ProEt.mk (𝟙 (X K))
private abbrev B := swapObject K h2

private def yArrow : Y K ⟶ T K :=
  MorphismProperty.Over.homMk (chartOpen K) (Category.comp_id _)

private def bArrow : B K h2 ⟶ T K :=
  MorphismProperty.Over.homMk (coverMap K ≫ affineOpen K) (Category.comp_id _)

private theorem empty_pullback_of_range_complement {A B X : Scheme.{0}} (f : A ⟶ X) (g : B ⟶ X)
    (h : Set.range f ⊆ (Set.range g)ᶜ) : IsEmpty (↥(pullback f g : Scheme.{0})) := by
  constructor
  intro x
  have hEq : f (pullback.fst f g x) = g (pullback.snd f g x) :=
    congrArg (fun k : pullback f g ⟶ X ↦ k x) (pullback.condition (f := f) (g := g))
  exact h ⟨pullback.fst f g x, rfl⟩ ⟨pullback.snd f g x, hEq.symm⟩

private theorem yOriginEmpty : IsEmpty (↥(pullback (chartOpen K) (projectiveOrigin K) : Scheme.{0})) := by
  apply empty_pullback_of_range_complement
  rw [← NodalSmoothRationalBoundary.smooth_range K]
  rintro _ ⟨y, rfl⟩
  let f := chartOpen K
  let q := NodalProjectiveClosure.projectiveNodeToBase K
  letI : Smooth (f ≫ q) := NodalSmoothLocus.chartOpen_smooth K
  have hy : f y ∈ q.smoothLocus := by
    apply (f.mem_preimage).mp
    rw [f.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    trivial
  exact ⟨⟨f y, hy⟩, rfl⟩

private theorem separatorCover :
    Sieve.ofArrows (coverObjects (B K h2) (Y K)) (coverArrows (bArrow K h2) (yArrow K)) ∈
      Scheme.ProEt.topology (X K) (T K) := by
  letI : Etale (coverMap K) := coverMap_etale K h2
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows (coverObjects (B K h2) (Y K))
      (coverArrows (bArrow K h2) (yArrow K))).map (Scheme.ProEt.forget (X K) ⋙ Over.forget (X K)) ∈
    Scheme.proetalePrecoverage (X K)
  rw [Presieve.map_ofArrows]
  apply Scheme.etalePrecoverage_le_proetalePrecoverage _
  apply (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
  refine ⟨?_, fun i ↦ ?_⟩
  · intro x
    have h : Set.range (affineOpen K) ∪ Set.range (chartOpen K) = Set.univ :=
      congrArg (fun U : (X K).Opens ↦ (U : Set (X K))) (NodalChartIntersection.charts_cover K)
    have hx : x ∈ Set.range (affineOpen K) ∪ Set.range (chartOpen K) := h.symm ▸ Set.mem_univ x
    rcases hx with ⟨z, hz⟩ | ⟨y, hy⟩
    · obtain ⟨w, hw⟩ := coverMap_surjective K h2 z
      exact ⟨false, w, (congrArg (affineOpen K) hw).trans hz⟩
    · exact ⟨true, y, hy⟩
  · cases i
    · change Etale (coverMap K ≫ affineOpen K)
      infer_instance
    · change Etale (chartOpen K)
      infer_instance

/-- The literal constant binary label 1 lifts locally on the proper node,
via the genuine crossed cover on Z and the empty conductor on Y. -/
theorem terminal_binary_cover :
    Presheaf.imageSieve
      (binaryDifference (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2)).hom
      (oneSection (q := projectiveOrigin K) (T K)) ∈ Scheme.ProEt.topology (X K) (T K) := by
  letI := projectiveOrigin_closed K
  apply (Scheme.ProEt.topology (X K)).superset_covering _ (separatorCover K h2)
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨i⟩
  cases i
  · refine ⟨separator K h2, ?_⟩
    change _ = (functionsOver Binary (projectiveOrigin K)).obj.map (bArrow K h2).op _
    rw [oneSection_restrict]
    exact separator_difference K h2
  · refine ⟨0, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact ((yOriginEmpty K).false x).elim

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

/-- The actual discrete-coefficient branch difference on the proper node is Epi. -/
theorem difference_epi :
    Epi (difference (normalizationMap K) (projectiveOrigin K)
      (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2) M) := by
  letI := projectiveOrigin_closed K
  exact ProetaleBranchDifferenceEpi.epi_of_terminal_binary
    (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2) M (terminal_binary_cover K h2)

end
end ManuscriptAudit.NodalProetaleConductorEpi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProetaleConductorEpi.terminal_binary_cover,
      ``ManuscriptAudit.NodalProetaleConductorEpi.difference_epi] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
