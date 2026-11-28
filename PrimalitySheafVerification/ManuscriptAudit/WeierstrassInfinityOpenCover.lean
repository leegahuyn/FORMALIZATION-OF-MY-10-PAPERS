import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Restrict
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityPuncture
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietoris

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

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

local instance : IsOpenImmersion (neighborhoodOpen W) := neighborhoodOpen_isOpenImmersion W

theorem cover :
    Set.range (neighborhoodOpen W) ∪ Set.range (affineOpen W) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases h : x ∈ Set.range (affineOpen W)
  · exact Or.inr h
  · left
    have h' : x ∈ Set.range (atInfinity W) := by
      rw [range_atInfinity]
      exact h
    obtain ⟨p, hp⟩ := h'
    refine ⟨originToNeighborhood W p, ?_⟩
    change (originToNeighborhood W ≫ neighborhoodOpen W) p = x
    rw [originToNeighborhood_fac]
    exact hp

abbrev Puncture := Localization.Away (localX W)

def punctureToNeighborhood :
    Spec (CommRingCat.of (Puncture W)) ⟶ neighborhoodScheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap (Neighborhood W) (Puncture W)))

private theorem overlap_range :
    Set.range (pullback.fst (neighborhoodOpen W) (affineOpen W)) =
      Set.range (punctureToNeighborhood W) := by
  change ((pullback.fst (neighborhoodOpen W) (affineOpen W)).opensRange : Set (neighborhoodScheme W)) =
    ((punctureToNeighborhood W).opensRange : Set (neighborhoodScheme W))
  rw [Scheme.Hom.opensRange_pullbackFst, preimage_affineOpen]
  unfold punctureToNeighborhood
  rw [Scheme.Hom.opensRange_localizationAway]

/-- The actual intersection in the proper closure is the principal-open spectrum. -/
def overlapIso :
    pullback (neighborhoodOpen W) (affineOpen W) ≅ Spec (CommRingCat.of (Puncture W)) :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst (neighborhoodOpen W) (affineOpen W))
    (punctureToNeighborhood W) (overlap_range W)

theorem overlapIso_fac :
    (overlapIso W).hom ≫ punctureToNeighborhood W = pullback.fst (neighborhoodOpen W) (affineOpen W) := by
  unfold overlapIso
  simp

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
