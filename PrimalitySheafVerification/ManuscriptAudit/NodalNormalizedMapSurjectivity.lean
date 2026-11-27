import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeAffineMap
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection

/-! Surjectivity of the actual proper normalization follows in the two
displayed Cartesian charts. -/

namespace ManuscriptAudit.NodalNormalizedMapSurjectivity

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode affineOpen)
open NodalProjectiveNormalization (normalizationMap)
open NodalProperYChart (chartOpen)
open NodalNormalizedNativeCharts
open NodalNormalizedNativeAffineMap
open NodalNormalizationFiber (affineLine affineNormalization affineNormalization_surjective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

theorem chartRanges : Set.range (affineOpen K) ∪ Set.range (chartOpen K) = Set.univ :=
  congrArg (fun U : (projectiveNode K).Opens ↦ (U : Set (projectiveNode K)))
    (NodalChartIntersection.charts_cover K)

/-- The actual normalization of the proper split node is surjective on points. -/
theorem properNormalization_surjective (h2 : (2 : K) ≠ 0) : Surjective (normalizationMap K) := by
  constructor
  intro x
  have hx : x ∈ Set.range (affineOpen K) ∪ Set.range (chartOpen K) :=
    (chartRanges K).symm ▸ Set.mem_univ x
  rcases hx with ⟨z, hz⟩ | ⟨y, hy⟩
  · obtain ⟨t, ht⟩ := affineNormalization_surjective K h2 z
    refine ⟨zToNormalized K h2 t, ?_⟩
    have h := congrArg (fun f : affineLine K ⟶ projectiveNode K ↦ f t)
      (zToNormalized_affine_isPullback K h2).w
    exact h.trans ((congrArg (affineOpen K) ht).trans hz)
  · refine ⟨yToNormalized K y, ?_⟩
    have h := congrArg (fun f : NodalYChartImmersion.nodeYChart K ⟶ projectiveNode K ↦ f y)
      (yToNormalized_over K)
    exact h.trans hy

end
end ManuscriptAudit.NodalNormalizedMapSurjectivity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedMapSurjectivity.chartRanges,
      ``ManuscriptAudit.NodalNormalizedMapSurjectivity.properNormalization_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
