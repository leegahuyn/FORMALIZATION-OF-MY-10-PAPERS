import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteCompactHTwoEquiv
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineSmoothCompactOpen
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeFiniteHTwoNormalizerImage
import PrimalitySheafVerification.ManuscriptAudit.ProetaleExactDirectImageCohomology

/-! Actual native finite compact support of the affine nodal smooth
locus agrees with its proper degree-two normalization image. -/

namespace ManuscriptAudit.NodalFiniteCompactHTwoNormalization

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (affineNode affineOpen projectiveNode projectiveNodeToBase)
open NodalRationalInfinity (infinityPoint infinityPoint_isClosedImmersion affine_complement_eq_infinity)
open NodalAffineSmoothCompactOpen (affineSmoothOpen compactOpen)
open NodalSmoothLocusOverlap (smoothOpen)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed smooth_range)
open NodalAffineOrigin (originMap)
open NodalProjectiveNormalization (normalizationMap normalizedNode)
open ProetaleContinuousDirectImageMaps (functions functionsOver)
open OpenProetaleExtension (extensionByZero)
open ProetaleBaseChange (directImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.{1}
private abbrev j := affineOpen K
private abbrev v := (affineSmoothOpen K).ι

/-- The affine relative smooth open omits the actual affine rational node. -/
theorem affine_smooth_complement :
    Set.range (v K) = (Set.range (originMap K))ᶜ := by
  have hPre : (j K) ⁻¹ᵁ smoothOpen K = affineSmoothOpen K :=
    (j K).preimage_smoothLocus_eq (projectiveNodeToBase K)
  ext x
  rw [Scheme.Opens.range_ι, ← hPre]
  change (j K) x ∈ (smoothOpen K : Set (projectiveNode K)) ↔ x ∉ Set.range (originMap K)
  rw [← Scheme.Opens.range_ι, smooth_range]
  show ((j K) x ∉ Set.range (projectiveOrigin K)) ↔ x ∉ Set.range (originMap K)
  have he : (j K) x ∈ Set.range (projectiveOrigin K) ↔ x ∈ Set.range (originMap K) := by
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, (j K).isOpenEmbedding.injective ?_⟩
      exact ht
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  exact not_congr he

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalAddGroup M] [Finite M]

abbrev compact := Sheaf.H ((extensionByZero (compactOpen K) A).obj
  (functions M (affineSmoothOpen K).toScheme)) 2

/-- Actual proper degree two equals the compact degree-two smooth affine group. -/
def ambientEquiv : compact K M ≃+ Sheaf.H (functions M (projectiveNode K)) 2 := by
  letI := infinityPoint_isClosedImmersion K
  letI : IsClosedImmersion (originMap K ≫ j K) := projectiveOrigin_closed K
  let e := ProetaleFiniteCompactHTwoEquiv.nestedEquiv K M (v K) (j K) (originMap K)
    (affine_smooth_complement K)
  exact e.trans (ProetaleFiniteCompactHTwoEquiv.singleEquiv K M (j K) (infinityPoint K) (by
    rw [← affine_complement_eq_infinity K, compl_compl]))

/-- The actual conductor identifies this native compact group with the
normalization direct-image coefficient cohomology. -/
def normalizationImageEquiv (h₂ : (2 : K) ≠ 0) :
    compact K M ≃+ Sheaf.H (functionsOver M (normalizationMap K)) 2 :=
  (ambientEquiv K M).trans (NodalNativeFiniteHTwoNormalizerImage.normalizationImageEquiv K M h₂)

/-- If the normalizer's actual direct image preserves epimorphisms, the
same canonical cohomology lands on the normalization itself. -/
def normalizationEquiv (h₂ : (2 : K) ≠ 0)
    [(directImage (normalizationMap K) A).PreservesEpimorphisms] :
    compact K M ≃+ Sheaf.H (functions M (normalizedNode K)) 2 :=
  (normalizationImageEquiv K M h₂).trans
    (ProetaleExactDirectImageCohomology.continuousEquiv (normalizationMap K) M 2)

end
end ManuscriptAudit.NodalFiniteCompactHTwoNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalFiniteCompactHTwoNormalization.ambientEquiv,
      ``ManuscriptAudit.NodalFiniteCompactHTwoNormalization.normalizationImageEquiv,
      ``ManuscriptAudit.NodalFiniteCompactHTwoNormalization.normalizationEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
