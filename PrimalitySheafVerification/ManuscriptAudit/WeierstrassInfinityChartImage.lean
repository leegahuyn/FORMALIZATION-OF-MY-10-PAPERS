import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartRegular
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityOverlapPlane

/-! The two ambient Weierstrass chart maps have the same schematic-image ideal. -/

namespace ManuscriptAudit.WeierstrassInfinityChartImage

open AlgebraicGeometry CategoryTheory
open WeierstrassInfinityChartCoordinates (affineY)
open WeierstrassInfinityChartOverlap
open WeierstrassInfinityOverlapPlane
open scoped Polynomial.Bivariate nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private theorem affineY_ne_zero : affineY W ≠ 0 := by
  simpa only [affineY, WeierstrassCurve.Affine.CoordinateRing.YClass, map_zero, sub_zero] using
    (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero (W' := W) (0 : Polynomial K))

theorem localizeAffine_injective : Function.Injective (localizeAffine W) :=
  IsLocalization.injective (M := Submonoid.powers (affineY W)) (ZOverlap W)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (affineY_ne_zero W))

private theorem overlapEquiv_algebraMap (r : C₀ W) :
    overlapEquiv W (algebraMap (C₀ W) (YOverlap W) r) = toZChart W r := by
  change toZOverlap W (algebraMap (C₀ W) (YOverlap W) r) = _
  unfold toZOverlap
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl

theorem toZChart_injective : Function.Injective (toZChart W) := by
  intro a b h
  apply IsLocalization.injective (M := Submonoid.powers (WeierstrassInfinityChartAlgebra.z W))
      (YOverlap W)
      (Submonoid.powers_le.mpr (WeierstrassInfinityChartRegular.z_regular W))
  apply (overlapEquiv W).injective
  simpa only [overlapEquiv_algebraMap] using h

private theorem specMap_dominant_of_injective {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (hf : Function.Injective f) : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap f)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := f)).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

/-- Both descriptions give the same closed schematic image in the actual projective plane. -/
theorem zKernel_yKernel : (WeierstrassProjectiveClosure.inPlane W).ker =
    (WeierstrassInfinityChartImmersion.inPlane W).ker := by
  letI : IsDomain (ZOverlap W) := Localization.Away.isDomain (affineY_ne_zero W)
  letI : IsReduced (C₀ W) :=
    isReduced_of_injective (toZChart W).toRingHom (toZChart_injective W)
  letI : IsDominant (toAffine W) :=
    specMap_dominant_of_injective _ (localizeAffine_injective W)
  letI : IsDominant (toInfinityChart W) :=
    specMap_dominant_of_injective _ (toZChart_injective W)
  letI : IsSchemeTheoreticallyDominant (toAffine W) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  letI : IsSchemeTheoreticallyDominant (toInfinityChart W) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hZ : (toAffine W ≫ WeierstrassProjectiveClosure.inPlane W).ker =
      (WeierstrassProjectiveClosure.inPlane W).ker := by
    rw [Scheme.Hom.ker_comp, (toAffine W).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hY : (toInfinityChart W ≫ WeierstrassInfinityChartImmersion.inPlane W).ker =
      (WeierstrassInfinityChartImmersion.inPlane W).ker := by
    rw [Scheme.Hom.ker_comp, (toInfinityChart W).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  exact hZ.symm.trans ((congrArg Scheme.Hom.ker (plane_overlap_eq W)).trans hY)

end

end ManuscriptAudit.WeierstrassInfinityChartImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityChartImage.localizeAffine_injective,
      ``ManuscriptAudit.WeierstrassInfinityChartImage.toZChart_injective,
      ``ManuscriptAudit.WeierstrassInfinityChartImage.zKernel_yKernel] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
