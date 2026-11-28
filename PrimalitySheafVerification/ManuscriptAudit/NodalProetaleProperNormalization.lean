import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleAffineNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeAffineMap
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestrictionEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageIdentity
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift

/-! Exact direct image on the actual proper nodal normalization. -/

namespace ManuscriptAudit.NodalProetaleProperNormalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode affineNode affineOpen)
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalProperYChart (chartOpen)
open NodalYChartImmersion (nodeYChart)
open NodalNormalizedNativeCharts (yToNormalized yToNormalized_isPullback zToNormalized)
open NodalNormalizedNativeAffineMap (zToNormalized_affine_isPullback)
open TwoOpenCokernelLift (coverObjects coverArrows)
open ProetaleBaseChange (directImage)
open ProetaleObjectRestriction (restriction restrictionAdjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private def cover : (projectiveNode K).OpenCover := by
  let d := coverArrows (chartOpen K) (affineOpen K)
  refine ⟨⟨Bool, coverObjects (nodeYChart K) (affineNode K), d⟩, ?_⟩
  apply (Scheme.ofArrows_mem_precoverage_iff @IsOpenImmersion).mpr
  refine ⟨?_, fun i ↦ ?_⟩
  · have hs : Set.range (chartOpen K) ∪ Set.range (affineOpen K) = Set.univ := by
      rw [Set.union_comm]
      exact congrArg (fun U : (projectiveNode K).Opens ↦ (U : Set (projectiveNode K)))
        (NodalChartIntersection.charts_cover K)
    intro x
    have hx : x ∈ Set.range (chartOpen K) ∪ Set.range (affineOpen K) :=
      hs.symm ▸ Set.mem_univ x
    rcases hx with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact ⟨false, a, ha⟩
    · exact ⟨true, b, hb⟩
  · cases i <;> infer_instance

private abbrev A := AddCommGrpCat.{1}

private theorem restrict_epi {X Y U V : Scheme.{0}} {f : Y ⟶ X} {j : U ⟶ X}
    {p : V ⟶ Y} {q : V ⟶ U} [WeaklyEtale j] [WeaklyEtale p]
    (H : IsPullback p q f j)
    {F G : Sheaf (Scheme.ProEt.topology Y) A} (α : F ⟶ G)
    (h : Epi ((directImage q A).map ((restriction p A).map α))) :
    Epi ((restriction j A).map ((directImage f A).map α)) := by
  let e := ProetaleDirectImageRestrictionPullback.directImageRestrictionIso H
  letI := h
  apply (epi_comp_iff_of_isIso _ (e.hom.app G)).mp
  change Epi (((directImage f A ⋙ restriction j A).map α) ≫ e.hom.app G)
  rw [e.hom.naturality]
  infer_instance

/-- The actual proper normalization takes epimorphisms to epimorphisms
on native pro-étale abelian sheaves. -/
theorem map_epi (h2 : (2 : K) ≠ 0)
    {F G : Sheaf (Scheme.ProEt.topology (normalizedNode K)) A} (α : F ⟶ G) [Epi α] :
    Epi ((directImage (normalizationMap K) A).map α) := by
  apply ProetaleOpenRestrictionEpi.epi_of_openCover (cover K)
  intro i
  cases i
  · change Epi ((restriction (chartOpen K) A).map
      ((directImage (normalizationMap K) A).map α))
    let p := yToNormalized K
    letI : (restriction p A).IsLeftAdjoint := (restrictionAdjunction p A).isLeftAdjoint
    letI : Epi ((restriction p A).map α) := (restriction p A).map_epi α
    exact restrict_epi (yToNormalized_isPullback K) α
      (ProetaleDirectImageIdentity.map_epi _ ((restriction p A).map α))
  · change Epi ((restriction (affineOpen K) A).map
      ((directImage (normalizationMap K) A).map α))
    let p := zToNormalized K h2
    letI : (restriction p A).IsLeftAdjoint := (restrictionAdjunction p A).isLeftAdjoint
    letI : Epi ((restriction p A).map α) := (restriction p A).map_epi α
    exact restrict_epi (zToNormalized_affine_isPullback K h2) α
      (NodalProetaleAffineNormalization.map_epi K h2 ((restriction p A).map α))

end
end ManuscriptAudit.NodalProetaleProperNormalization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProetaleProperNormalization.map_epi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
