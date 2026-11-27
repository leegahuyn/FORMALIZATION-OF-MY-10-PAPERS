import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeCharts
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenLocalLifts
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift

/-! The displayed normalized nodal charts form an actual two-open
cover with its principal localization pullback in the native site. -/

namespace ManuscriptAudit.NodalNormalizedNativeCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode affineOpen)
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalProperYChart (chartOpen)
open NodalYChartImmersion (nodeYChart)
open NodalYChartOverlap (overlapRing)
open NodalYChartPrincipalOpen (principalInclusion)
open NodalNormalizedNativeCharts
open ProetaleOpenLocalLifts
open TwoOpenCokernelLift (coverObjects coverArrows)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

theorem charts_cover :
    Set.range (yToNormalized K) ∪ Set.range (zToNormalized K h2) = Set.univ := by
  let Y := nodeYChart K
  let B := NodalProjectiveClosure.affineNode K
  let X := projectiveNode K
  let N := normalizedNode K
  let d := coverArrows (chartOpen K) (affineOpen K)
  let p := coverArrows (yToNormalized K) (zToNormalized K h2)
  let q : (i : Bool) → coverObjects Y (Spec (CommRingCat.of (Polynomial K))) i ⟶ coverObjects Y B i
    | false => 𝟙 Y
    | true => zToAffine K h2
  have hRanges : Set.range (chartOpen K) ∪ Set.range (affineOpen K) = Set.univ := by
    rw [Set.union_comm]
    exact congrArg (fun U : X.Opens ↦ (U : Set X)) (NodalChartIntersection.charts_cover K)
  have hd : Presieve.ofArrows (coverObjects Y B) d ∈ Scheme.precoverage @Etale X := by
    apply (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
    refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
    · have hx : x ∈ Set.range (chartOpen K) ∪ Set.range (affineOpen K) :=
        hRanges.symm ▸ Set.mem_univ x
      rcases hx with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨false, a, ha⟩
      · exact ⟨true, b, hb⟩
    · cases i
      · change Etale (chartOpen K)
        infer_instance
      · change Etale (affineOpen K)
        infer_instance
  have hp : Presieve.ofArrows (coverObjects Y (Spec (CommRingCat.of (Polynomial K)))) p ∈
      Scheme.precoverage @Etale N :=
    Precoverage.mem_coverings_of_isPullback d hd (normalizationMap K) p q (fun i ↦ by
      cases i
      · exact yToNormalized_isPullback K
      · exact zToNormalized_isPullback K h2)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, w, hw⟩ := ((Scheme.ofArrows_mem_precoverage_iff @Etale).mp hp).1 x
  cases i
  · exact Or.inl ⟨w, hw⟩
  · exact Or.inr ⟨w, hw⟩

/-- The actual principal localization viewed in the normalization's pro-étale site. -/
abbrev overlapObject : (normalizedNode K).ProEt :=
  Scheme.ProEt.mk (principalInclusion K ≫ yToNormalized K)

abbrev firstLeg : overlapObject K ⟶ openObject (yToNormalized K) :=
  MorphismProperty.Over.homMk (principalInclusion K) (by
    change principalInclusion K ≫ 𝟙 (nodeYChart K) ≫ yToNormalized K = _
    rw [Category.id_comp])

abbrev secondLeg : overlapObject K ⟶ openObject (zToNormalized K h2) :=
  MorphismProperty.Over.homMk (overlapToZ K h2) (by
    change overlapToZ K h2 ≫ 𝟙 (Spec (CommRingCat.of (Polynomial K))) ≫ zToNormalized K h2 =
      principalInclusion K ≫ yToNormalized K
    simpa only [Category.id_comp] using (overlap_isPullback K h2).w.symm)

theorem native_overlap_isPullback :
    IsPullback (firstLeg K) (secondLeg K h2)
      (openArrow (yToNormalized K)) (openArrow (zToNormalized K h2)) :=
  ProetaleAffineTensor.underlying_isPullback (overlap_isPullback K h2)

end
end ManuscriptAudit.NodalNormalizedNativeCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedNativeCover.charts_cover,
      ``ManuscriptAudit.NodalNormalizedNativeCover.native_overlap_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
