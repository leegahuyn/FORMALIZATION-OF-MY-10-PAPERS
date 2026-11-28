import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityNeighborhood
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveBoundary

/-! Near the unique rational boundary, the original affine chart is the
puncture where the regular prime parameter X/Y is invertible. -/

namespace ManuscriptAudit.WeierstrassInfinityPuncture

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassInfinityChartAlgebra
open WeierstrassCartierInfinity WeierstrassInfinityOriginIdeal
open CuspProperCompactification (affineZChartι)
open CuspYChartAlgebra (grading X_mem_one)
open scoped nonZeroDivisors

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

theorem affineOpen_range_z :
    (affineOpen W).opensRange =
      (inPlane W).imageι ⁻¹ᵁ Proj.basicOpen (grading K) (CuspYChartAlgebra.z K) := by
  apply SetLike.coe_injective
  ext p
  change p ∈ Set.range (affineOpen W) ↔
    (inPlane W).imageι p ∈ Proj.basicOpen (grading K) (CuspYChartAlgebra.z K)
  constructor
  · rintro ⟨a, rfl⟩
    change ((affineOpen W) ≫ (inPlane W).imageι) a ∈ _
    rw [affineOpen, Scheme.Hom.toImage_imageι]
    unfold inPlane
    change affineZChartι K (Spec.map (CommRingCat.ofHom (chartEvaluation W)) a) ∈ _
    rw [← Proj.opensRange_awayι (grading K) (CuspYChartAlgebra.z K) (X_mem_one K 2) (by decide)]
    exact ⟨_, rfl⟩
  · intro hp
    by_contra hn
    exact ((Proj.mem_basicOpen _ _ _).mp hp)
      (WeierstrassProjectiveBoundary.boundary_plane_coordinates W p hn).2.1

private theorem local_relation :
    localZ W * algebraMap (Ring W) (Neighborhood W) (bracket W) = localX W ^ 3 := by
  simpa only [localX, localZ, map_mul, map_pow] using
    congrArg (algebraMap (Ring W) (Neighborhood W)) (relation W)

theorem z_open_eq_x :
    PrimeSpectrum.basicOpen (localZ W) = PrimeSpectrum.basicOpen (localX W) := by
  apply SetLike.coe_injective
  ext q
  change (localZ W ∉ q.asIdeal) ↔ (localX W ∉ q.asIdeal)
  apply not_congr
  constructor
  · intro hz
    apply q.isPrime.mem_of_pow_mem 3
    rw [← local_relation]
    exact q.asIdeal.mul_mem_right _ hz
  · intro hx
    have h3 : localX W ^ 3 ∈ q.asIdeal := by
      rw [pow_succ]
      exact q.asIdeal.mul_mem_left _ hx
    obtain ⟨b, hb⟩ := IsLocalization.Away.algebraMap_isUnit (S := Neighborhood W) (bracket W)
    have hb' : localZ W * (b : Neighborhood W) ∈ q.asIdeal := by
      rwa [hb, local_relation]
    have hv := q.asIdeal.mul_mem_right (↑(b⁻¹) : Neighborhood W) hb'
    simpa only [mul_assoc, Units.mul_inv, mul_one] using hv

/-- The overlap with the affine curve is the principal open D(X/Y) in the
actual open neighborhood of the unique boundary point. -/
theorem preimage_affineOpen :
    (neighborhoodOpen W) ⁻¹ᵁ (affineOpen W).opensRange = PrimeSpectrum.basicOpen (localX W) := by
  rw [affineOpen_range_z, ← Scheme.Hom.comp_preimage]
  unfold neighborhoodOpen
  rw [Category.assoc, WeierstrassProperInfinityChart.chartOpen_inPlane,
    Scheme.Hom.comp_preimage, WeierstrassInfinityChartImmersion.inPlane_preimage_z]
  unfold neighborhoodToChart
  rw [SpecMap_preimage_basicOpen]
  exact z_open_eq_x W

theorem localX_prime : Prime (localX W) := by
  have hne : localX W ≠ 0 := by
    intro h
    have h1 : (1 : Neighborhood W) = 0 :=
      (mem_nonZeroDivisors_iff_left.mp (WeierstrassInfinityChartRegular.localX_regular W)) 1
        (by rw [h, zero_mul])
    exact one_ne_zero (by simpa only [map_one, map_zero] using congrArg (localOrigin W) h1)
  apply (Ideal.span_singleton_prime hne).mp
  rw [← localOrigin_ker]
  exact RingHom.ker_isPrime _

end

end ManuscriptAudit.WeierstrassInfinityPuncture

namespace ManuscriptAudit.WeierstrassInfinityOpenCover

open AlgebraicGeometry CategoryTheory
open WeierstrassInfinityChartAlgebra WeierstrassCartierInfinity

universe u
noncomputable section

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

abbrev Puncture := Localization.Away (localX W)

def punctureToNeighborhood :
    Spec (CommRingCat.of (Puncture W)) ⟶ neighborhoodScheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap (Neighborhood W) (Puncture W)))

instance punctureToNeighborhood_isOpenImmersion : IsOpenImmersion (punctureToNeighborhood W) :=
  IsOpenImmersion.of_isLocalization (localX W)

end

end ManuscriptAudit.WeierstrassInfinityOpenCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityPuncture.affineOpen_range_z,
      ``ManuscriptAudit.WeierstrassInfinityPuncture.z_open_eq_x,
      ``ManuscriptAudit.WeierstrassInfinityPuncture.preimage_affineOpen,
      ``ManuscriptAudit.WeierstrassInfinityPuncture.localX_prime] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
