import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Restrict
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityPuncture
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietoris
import PrimalitySheafVerification.ManuscriptAudit.EtaleOpenIntersection

/-! The true projective Weierstrass closure is covered by the original affine
chart and the principal Cartier neighborhood. Their pullback is the actual
principal-open spectrum, so the native Mayer–Vietoris sequence applies. -/

namespace ManuscriptAudit.WeierstrassInfinityOpenCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassProjectiveClosure WeierstrassCartierInfinity
open WeierstrassInfinityChartAlgebra WeierstrassInfinityPuncture
open EtaleOpenIntersection

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt MvPolynomial.gradedAlgebra

local instance : IsOpenImmersion (neighborhoodOpen W) := neighborhoodOpen_isOpenImmersion W

private theorem chart_preimage_affine :
    (WeierstrassProperInfinityChart.chartOpen W) ⁻¹ᵁ (affineOpen W).opensRange =
      PrimeSpectrum.basicOpen (WeierstrassInfinityChartAlgebra.z W) := by
  rw [affineOpen_range_z, ← Scheme.Hom.comp_preimage,
    WeierstrassProperInfinityChart.chartOpen_inPlane, WeierstrassInfinityChartImmersion.inPlane_preimage_z]

private theorem bracket_nonmem_of_z_mem
    (q : PrimeSpectrum (Ring W))
    (hz : WeierstrassInfinityChartAlgebra.z W ∈ q.asIdeal) : bracket W ∉ q.asIdeal := by
  have hx : WeierstrassInfinityChartAlgebra.x W ∈ q.asIdeal := by
    apply q.isPrime.mem_of_pow_mem 3
    rw [← relation]
    exact q.asIdeal.mul_mem_right _ hz
  have hSpan : Ideal.span ({WeierstrassInfinityChartAlgebra.x W,
      WeierstrassInfinityChartAlgebra.z W} : Set (Ring W)) ≤ q.asIdeal := by
    rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hx, hz⟩
  have hd : bracket W - 1 ∈ Ideal.span ({WeierstrassInfinityChartAlgebra.x W,
      WeierstrassInfinityChartAlgebra.z W} : Set (Ring W)) := by
    rw [← WeierstrassInfinityOriginIdeal.origin_ker]
    change origin W (bracket W - 1) = 0
    rw [map_sub, origin_bracket, map_one, sub_self]
  intro hb
  have hOne : (1 : Ring W) ∈ q.asIdeal := by
    simpa only [sub_sub_cancel] using q.asIdeal.sub_mem hb (hSpan hd)
  exact q.isPrime.ne_top ((Ideal.eq_top_iff_one q.asIdeal).mpr hOne)

/-- The actual affine curve and Cartier neighborhood cover its projective
closure. The cover follows from the homogeneous coordinates of boundary points. -/
theorem cover :
    Set.range (neighborhoodOpen W) ∪ Set.range (affineOpen W) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases h : x ∈ Set.range (affineOpen W)
  · exact Or.inr h
  · left
    have hY : x ∈ WeierstrassProperInfinityChart.yOpen W := by
      change (inPlane W).imageι x ∈ Proj.basicOpen (CuspYChartAlgebra.grading K) (CuspYChartAlgebra.y K)
      exact (Proj.mem_basicOpen _ _ _).mpr
        (WeierstrassProjectiveBoundary.boundary_plane_coordinates W x h).2.2
    rw [← WeierstrassProperInfinityChart.chartOpen_range] at hY
    obtain ⟨q, hq⟩ := hY
    let q₀ : PrimeSpectrum (Ring W) := q
    have hz : WeierstrassInfinityChartAlgebra.z W ∈ q₀.asIdeal := by
      by_contra hn
      have hp : q ∈ (WeierstrassProperInfinityChart.chartOpen W) ⁻¹ᵁ (affineOpen W).opensRange := by
        rw [chart_preimage_affine]
        exact hn
      apply h
      change WeierstrassProperInfinityChart.chartOpen W q ∈ Set.range (affineOpen W) at hp
      rwa [hq] at hp
    letI : IsOpenImmersion (neighborhoodToChart W) := IsOpenImmersion.of_isLocalization (bracket W)
    have hN : q ∈ (neighborhoodToChart W).opensRange := by
      have hRange :
          (neighborhoodToChart W).opensRange = PrimeSpectrum.basicOpen (bracket W) :=
        Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Ring W)) (bracket W)
      rw [hRange]
      exact bracket_nonmem_of_z_mem W q₀ hz
    obtain ⟨u, hu⟩ := hN
    refine ⟨u, ?_⟩
    rw [neighborhoodOpen, Scheme.Hom.comp_apply, hu, hq]

private theorem overlap_range :
    Set.range (pullback.fst (neighborhoodOpen W) (affineOpen W)) =
      Set.range (punctureToNeighborhood W) := by
  change ((pullback.fst (neighborhoodOpen W) (affineOpen W)).opensRange : Set (neighborhoodScheme W)) =
    ((punctureToNeighborhood W).opensRange : Set (neighborhoodScheme W))
  rw [Scheme.Hom.opensRange_pullbackFst, preimage_affineOpen]
  have hRange :
      (punctureToNeighborhood W).opensRange = PrimeSpectrum.basicOpen (localX W) :=
    Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Neighborhood W)) (localX W)
  rw [hRange]

/-- The actual intersection in the proper closure is the principal-open spectrum. -/
def overlapIso :
    pullback (neighborhoodOpen W) (affineOpen W) ≅ Spec (CommRingCat.of (Puncture W)) :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst (neighborhoodOpen W) (affineOpen W))
    (punctureToNeighborhood W) (overlap_range W)

set_option maxHeartbeats 700000 in
theorem overlapIso_fac :
    (overlapIso W).hom ≫ punctureToNeighborhood W = pullback.fst (neighborhoodOpen W) (affineOpen W) := by
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (overlap_range W)

/-- Native exact étale cohomology sequence of this actual projective cover. -/
theorem native_mayerVietoris_exact
    (F : Sheaf (projectiveScheme W).smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    (EtaleMayerVietoris.openCoverSequence (neighborhoodOpen W) (affineOpen W)
      (pullback.fst (neighborhoodOpen W) (affineOpen W) ≫ neighborhoodOpen W)
      (fstLeg (neighborhoodOpen W) (affineOpen W))
      (sndLeg (neighborhoodOpen W) (affineOpen W))
      (intersection_isPullback (neighborhoodOpen W) (affineOpen W))
      (cover W) F n).Exact :=
  EtaleMayerVietoris.openCoverSequence_exact _ _ _ _ _ _ _ _ _

end

end ManuscriptAudit.WeierstrassInfinityOpenCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityOpenCover.cover,
      ``ManuscriptAudit.WeierstrassInfinityOpenCover.overlapIso,
      ``ManuscriptAudit.WeierstrassInfinityOpenCover.overlapIso_fac,
      ``ManuscriptAudit.WeierstrassInfinityOpenCover.native_mayerVietoris_exact] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
