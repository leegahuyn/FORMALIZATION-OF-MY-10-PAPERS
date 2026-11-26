import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProperYChart
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveBoundary

/-! The two affine opens cover the proper nodal cubic. Their actual scheme
pullback is the normalized parameter line away from t(t²−1)=0. -/

namespace ManuscriptAudit.NodalChartIntersection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (affineOpen nodeInPlane projectiveNode)
open NodalProjectiveBoundary (boundary_plane_coordinates)
open NodalYChartImmersion (nodeYChart xCoeff yCoordinateRing)
open NodalProperYChart (chartOpen chartOpen_range yOpen chartOpen_preimage_affine
  chartOpen_inPlane)
open NodalYChartOverlap (overlapRing overlapEquiv toParameter)
open NodalYChartOverlapPlane (parameterScheme toNodeYChart toAffineNode plane_overlap_eq)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 140000

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

theorem charts_cover :
    (affineOpen K).opensRange ⊔ (chartOpen K).opensRange = ⊤ := by
  apply top_unique
  intro p _
  change p ∈ (affineOpen K).opensRange ∨ p ∈ (chartOpen K).opensRange
  by_cases hp : p ∈ Set.range (affineOpen K)
  · exact Or.inl hp
  · right
    rw [chartOpen_range]
    exact (Proj.mem_basicOpen _ _ _).mpr (boundary_plane_coordinates K p hp).2.2

private def localizedYToChart :
    Spec (CommRingCat.of (overlapRing K)) ⟶ nodeYChart K :=
  Spec.map (CommRingCat.ofHom (algebraMap (yCoordinateRing K) (overlapRing K)))

private instance : IsOpenImmersion (localizedYToChart K) :=
  IsOpenImmersion.of_isLocalization (S := overlapRing K) (xCoeff K)

private theorem localizedYToChart_range :
    (localizedYToChart K).opensRange = PrimeSpectrum.basicOpen (xCoeff K) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (overlapRing K) (xCoeff K)

theorem intersection_snd_opensRange :
    (pullback.snd (affineOpen K) (chartOpen K)).opensRange = PrimeSpectrum.basicOpen (xCoeff K) := by
  rw [Scheme.Hom.opensRange_pullbackSnd, chartOpen_preimage_affine]

private def intersectionIsoLocal :
    pullback (affineOpen K) (chartOpen K) ≅ Spec (CommRingCat.of (overlapRing K)) := by
  apply IsOpenImmersion.isoOfRangeEq (pullback.snd (affineOpen K) (chartOpen K))
    (localizedYToChart K)
  change ((pullback.snd (affineOpen K) (chartOpen K)).opensRange : Set (nodeYChart K)) =
    ((localizedYToChart K).opensRange : Set (nodeYChart K))
  rw [intersection_snd_opensRange, localizedYToChart_range]

private theorem intersectionIsoLocal_hom_snd :
    (intersectionIsoLocal K).hom ≫ localizedYToChart K =
      pullback.snd (affineOpen K) (chartOpen K) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private def parameterIsoLocal :
    parameterScheme K ≅ Spec (CommRingCat.of (overlapRing K)) :=
  Scheme.Spec.mapIso (overlapEquiv K).toRingEquiv.toCommRingCatIso.op

/-- The actual scheme overlap is the normalized parameter line away from t(t²−1)=0. -/
def intersectionIsoParameter :
    pullback (affineOpen K) (chartOpen K) ≅ parameterScheme K :=
  intersectionIsoLocal K ≪≫ (parameterIsoLocal K).symm

private theorem parameterIsoLocal_toChart :
    (parameterIsoLocal K).hom ≫ localizedYToChart K = toNodeYChart K := by
  change Spec.map (CommRingCat.ofHom (overlapEquiv K).toAlgHom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (yCoordinateRing K) (overlapRing K))) =
      Spec.map (CommRingCat.ofHom (NodalYChartOverlap.yToParameter K).toRingHom)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change toParameter K (algebraMap (yCoordinateRing K) (overlapRing K) a) =
    NodalYChartOverlap.yToParameter K a
  unfold toParameter
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl

@[reassoc]
theorem intersectionIsoParameter_inv_snd :
    (intersectionIsoParameter K).inv ≫ pullback.snd (affineOpen K) (chartOpen K) =
      toNodeYChart K := by
  have h : (intersectionIsoLocal K).inv ≫ pullback.snd (affineOpen K) (chartOpen K) =
      localizedYToChart K := by
    rw [← intersectionIsoLocal_hom_snd, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change ((parameterIsoLocal K).hom ≫ (intersectionIsoLocal K).inv) ≫
      pullback.snd (affineOpen K) (chartOpen K) = toNodeYChart K
  rw [Category.assoc, h, parameterIsoLocal_toChart]

@[reassoc]
theorem intersectionIsoParameter_inv_fst :
    (intersectionIsoParameter K).inv ≫ pullback.fst (affineOpen K) (chartOpen K) =
      toAffineNode K := by
  apply (cancel_mono (affineOpen K)).mp
  rw [Category.assoc, pullback.condition, ← Category.assoc, intersectionIsoParameter_inv_snd]
  apply (cancel_mono ((nodeInPlane K).imageι)).mp
  rw [Category.assoc, chartOpen_inPlane, Category.assoc, affineOpen, Scheme.Hom.toImage_imageι]
  exact (plane_overlap_eq K).symm

end
end ManuscriptAudit.NodalChartIntersection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalChartIntersection.charts_cover,
      ``ManuscriptAudit.NodalChartIntersection.intersection_snd_opensRange,
      ``ManuscriptAudit.NodalChartIntersection.intersectionIsoParameter,
      ``ManuscriptAudit.NodalChartIntersection.intersectionIsoParameter_inv_snd,
      ``ManuscriptAudit.NodalChartIntersection.intersectionIsoParameter_inv_fst] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
