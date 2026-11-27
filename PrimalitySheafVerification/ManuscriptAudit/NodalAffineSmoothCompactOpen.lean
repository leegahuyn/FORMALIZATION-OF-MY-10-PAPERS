import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalRationalInfinity
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothRationalBoundary
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveNormalization

/-! The actual relative smooth open of the affine nodal chart embeds in
the proper node with exactly its rational singular and infinity points omitted. -/

namespace ManuscriptAudit.NodalAffineSmoothCompactOpen

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (affineNode affineOpen projectiveNode projectiveNodeToBase projectiveNode_isProper)
open NodalRationalInfinity (infinityPoint infinityPoint_outside affine_complement_eq_infinity)
open NodalSmoothRationalBoundary (projectiveOrigin smooth_range)
open NodalSmoothLocus (nodePoint smoothLocus_eq_complement)
open NodalSmoothLocusOverlap (smoothOpen puncturedZ puncturedZRing puncturedZ_toAffine)
open NodalAffineOrigin (originMap originPoint prime_eq_origin_iff_x_mem)
open NodalAffinePresentation (nodeX)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

abbrev affineSmoothOpen := (affineOpen K ≫ projectiveNodeToBase K).smoothLocus

/-- The genuine open immersion from the smooth part of the actual affine chart to the proper node. -/
abbrev compactOpen : (affineSmoothOpen K).toScheme ⟶ projectiveNode K :=
  (affineSmoothOpen K).ι ≫ affineOpen K

private theorem smooth_preimage : (affineOpen K) ⁻¹ᵁ (smoothOpen K) = affineSmoothOpen K :=
  (affineOpen K).preimage_smoothLocus_eq (projectiveNodeToBase K)

theorem boundary_disjoint : Disjoint (Set.range (projectiveOrigin K)) (Set.range (infinityPoint K)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, rfl⟩ ⟨w, hw⟩
  have h : infinityPoint K w ∈ Set.range (affineOpen K) := ⟨originMap K z, hw.symm⟩
  have hz : w = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  exact infinityPoint_outside K (hz ▸ h)

private theorem range_intersection :
    Set.range (compactOpen K) = Set.range (affineOpen K) ∩ Set.range (smoothOpen K).ι := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z.1, rfl⟩, ?_⟩
    rw [Scheme.Opens.range_ι]
    have hz : z.1 ∈ (affineOpen K) ⁻¹ᵁ (smoothOpen K) := by
      rw [smooth_preimage K]
      exact z.property
    exact (affineOpen K).mem_preimage.mp hz
  · rintro ⟨⟨z, hz⟩, h⟩
    rw [Scheme.Opens.range_ι, ← hz] at h
    have hm := (affineOpen K).mem_preimage.mpr h
    rw [smooth_preimage K] at hm
    exact ⟨⟨z, hm⟩, hz⟩

/-- The actual affine smooth locus omits exactly the indicated two disjoint rational points. -/
theorem compactOpen_range :
    Set.range (compactOpen K) = (Set.range (projectiveOrigin K) ∪ Set.range (infinityPoint K))ᶜ := by
  have hAffine : Set.range (affineOpen K) = (Set.range (infinityPoint K))ᶜ := by
    rw [← affine_complement_eq_infinity K, compl_compl]
  rw [range_intersection K, hAffine, smooth_range K]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union, not_or, and_comm]

private theorem punctured_range :
    Set.range (puncturedZ_toAffine K) = Set.range (affineSmoothOpen K).ι := by
  rw [Scheme.Opens.range_ι]
  change Set.range (fun (q : PrimeSpectrum (puncturedZRing K)) ↦
    PrimeSpectrum.comap (algebraMap (NodalConductor.coordinates K) (puncturedZRing K)) q) = _
  rw [PrimeSpectrum.localization_away_comap_range (puncturedZRing K) (nodeX K)]
  ext q
  rw [← smooth_preimage K]
  change q ∈ PrimeSpectrum.basicOpen (nodeX K) ↔ q ∈ (affineOpen K) ⁻¹ᵁ (smoothOpen K)
  rw [PrimeSpectrum.mem_basicOpen, (affineOpen K).mem_preimage]
  change nodeX K ∉ q.asIdeal ↔ affineOpen K q ∈ ((projectiveNodeToBase K).smoothLocus : Set (projectiveNode K))
  rw [smoothLocus_eq_complement K]
  change nodeX K ∉ q.asIdeal ↔ affineOpen K q ≠ nodePoint K
  apply not_congr
  exact (prime_eq_origin_iff_x_mem K q).symm.trans
    ⟨congrArg (affineOpen K), fun h ↦ (affineOpen K).isOpenEmbedding.injective h⟩

/-- The punctured localization is the literal relative smooth open as a scheme. -/
def puncturedIso : puncturedZ K ≅ (affineSmoothOpen K).toScheme :=
  IsOpenImmersion.isoOfRangeEq (puncturedZ_toAffine K) (affineSmoothOpen K).ι (punctured_range K)

theorem compactOpen_quasiCompact : QuasiCompact (compactOpen K) := by
  letI : CompactSpace (puncturedZ K) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum (puncturedZRing K)))
  letI : CompactSpace (affineSmoothOpen K).toScheme := (puncturedIso K).hom.homeomorph.compactSpace
  letI : IsProper (projectiveNodeToBase K) := projectiveNode_isProper K
  letI : QuasiSeparatedSpace (projectiveNode K) := quasiSeparatedSpace_of_quasiSeparated (projectiveNodeToBase K)
  exact quasiCompact_of_compactSpace _

end
end ManuscriptAudit.NodalAffineSmoothCompactOpen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalAffineSmoothCompactOpen.boundary_disjoint,
      ``ManuscriptAudit.NodalAffineSmoothCompactOpen.compactOpen_range,
      ``ManuscriptAudit.NodalAffineSmoothCompactOpen.puncturedIso,
      ``ManuscriptAudit.NodalAffineSmoothCompactOpen.compactOpen_quasiCompact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
