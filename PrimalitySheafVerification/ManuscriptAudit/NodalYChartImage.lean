import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartOverlapPlane

/-! The common localization is scheme-theoretically dense in each nodal
chart, so their actual embeddings have the same schematic image. -/

namespace ManuscriptAudit.NodalYChartImage

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (nodeInPlane)
open NodalYChartImmersion (xCoeff yCoordinateRing coordinateEquiv nodeYInPlane)
open NodalYChartOverlap (parameterRing overlapRing yToParameter toParameter overlapEquiv)
open NodalYChartOverlapPlane (zParameter toAffineNode toNodeYChart plane_overlap_eq)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

private theorem away_algebraMap_injective {R : Type*} [CommRing R] [IsDomain R]
    {a : R} (ha : a ≠ 0) : Function.Injective (algebraMap R (Localization.Away a)) := by
  exact IsLocalization.injective (M := Submonoid.powers a) (Localization.Away a)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)

private theorem parameter_coefficient_ne_zero : (1 : Polynomial K) - Polynomial.X ^ 2 ≠ 0 := by
  intro h
  have h₀ := congrArg (Polynomial.eval (0 : K)) h
  norm_num at h₀

private theorem conductor_ne_zero : NodalConductor.x K ≠ 0 := by
  intro h
  have h₀ := congrArg (Polynomial.eval (0 : K)) h
  norm_num [NodalConductor.x] at h₀

private theorem denominator_ne_zero : NodalConductor.y K ≠ 0 :=
  mul_ne_zero (conductor_ne_zero K) Polynomial.X_ne_zero

theorem zParameter_injective : Function.Injective (zParameter K) :=
  (away_algebraMap_injective (denominator_ne_zero K)).comp Subtype.val_injective

theorem xCoeff_ne_zero : xCoeff K ≠ 0 := by
  intro h
  have hX := (coordinateEquiv K).commutes (Polynomial.X : Polynomial K)
  change coordinateEquiv K (xCoeff K) = _ at hX
  rw [h, map_zero] at hX
  exact Polynomial.X_ne_zero
    (away_algebraMap_injective (parameter_coefficient_ne_zero K) (hX.symm.trans (map_zero _).symm))

instance yCoordinateRing_isDomain : IsDomain (yCoordinateRing K) := by
  letI : IsDomain (Localization.Away ((1 : Polynomial K) - Polynomial.X ^ 2)) :=
    Localization.Away.isDomain (parameter_coefficient_ne_zero K)
  exact (coordinateEquiv K).toRingEquiv.toMulEquiv.isDomain _

private theorem overlapEquiv_algebraMap (a : yCoordinateRing K) :
    overlapEquiv K (algebraMap (yCoordinateRing K) (overlapRing K) a) = yToParameter K a := by
  change toParameter K (algebraMap (yCoordinateRing K) (overlapRing K) a) = _
  unfold toParameter
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl

theorem yToParameter_injective : Function.Injective (yToParameter K) := by
  intro a b h
  apply away_algebraMap_injective (xCoeff_ne_zero K)
  apply (overlapEquiv K).injective
  simpa only [overlapEquiv_algebraMap] using h

private theorem specMap_dominant_of_injective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap f)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := f)).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

/-- The actual affine nodal chart and the chart Y≠0 have the same
schematic-image ideal in the native projective plane. -/
theorem zKernel_yKernel : (nodeInPlane K).ker = (nodeYInPlane K).ker := by
  haveI : IsDominant (toAffineNode K) := specMap_dominant_of_injective _ (zParameter_injective K)
  haveI : IsDominant (toNodeYChart K) := specMap_dominant_of_injective _ (yToParameter_injective K)
  haveI : IsSchemeTheoreticallyDominant (toAffineNode K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  haveI : IsSchemeTheoreticallyDominant (toNodeYChart K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hZ : (toAffineNode K ≫ nodeInPlane K).ker = (nodeInPlane K).ker := by
    rw [Scheme.Hom.ker_comp, (toAffineNode K).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hY : (toNodeYChart K ≫ nodeYInPlane K).ker = (nodeYInPlane K).ker := by
    rw [Scheme.Hom.ker_comp, (toNodeYChart K).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  exact hZ.symm.trans ((congrArg Scheme.Hom.ker (plane_overlap_eq K)).trans hY)

end
end ManuscriptAudit.NodalYChartImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalYChartImage.zParameter_injective,
      ``ManuscriptAudit.NodalYChartImage.xCoeff_ne_zero,
      ``ManuscriptAudit.NodalYChartImage.yToParameter_injective,
      ``ManuscriptAudit.NodalYChartImage.zKernel_yKernel] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
