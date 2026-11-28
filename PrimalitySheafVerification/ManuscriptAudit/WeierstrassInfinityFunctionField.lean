import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.LocalizationLocalization
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartImage

/-! The affine Weierstrass function field agrees with the infinity chart's
fraction field through the actual projective overlap. -/

namespace ManuscriptAudit.WeierstrassInfinityFunctionField

open WeierstrassInfinityChartAlgebra
open WeierstrassInfinityChartCoordinates (affineY)
open WeierstrassInfinityChartOverlap (YOverlap ZOverlap overlapEquiv toZChart toZOverlap)
open scoped nonZeroDivisors

noncomputable section

private def localizationFieldLift {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R S] [Algebra R F] [IsFractionRing R F] (M : Submonoid R)
    [IsLocalization M S] (h : M ≤ nonZeroDivisors R) : S →+* F :=
  (IsLocalization.localizationAlgebraOfSubmonoidLe S F M (nonZeroDivisors R) h).toRingHom

private def localizationFieldEquiv {R S F : Type*} [CommRing R] [CommRing S] [Field F]
    [Algebra R S] [Algebra R F] [IsFractionRing R F] (M : Submonoid R)
    [IsLocalization M S] (h : M ≤ nonZeroDivisors R) : F ≃+* FractionRing S := by
  letI : Algebra S F :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S F M (nonZeroDivisors R) h
  letI : IsScalarTower R S F :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S F M (nonZeroDivisors R) h
  letI : IsFractionRing S F := IsFractionRing.isFractionRing_of_isLocalization M S F h
  exact (FractionRing.algEquiv S F).symm.toRingEquiv

private theorem localizationFieldEquiv_symm_apply {R S F : Type*} [CommRing R] [CommRing S]
    [Field F] [Algebra R S] [Algebra R F] [IsFractionRing R F] (M : Submonoid R)
    [IsLocalization M S] (h : M ≤ nonZeroDivisors R) (x : S) :
    (localizationFieldEquiv (S := S) (F := F) M h).symm (algebraMap S (FractionRing S) x) =
      localizationFieldLift (F := F) M h x := by
  letI : Algebra S F :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S F M (nonZeroDivisors R) h
  letI : IsScalarTower R S F :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S F M (nonZeroDivisors R) h
  letI : IsFractionRing S F := IsFractionRing.isFractionRing_of_isLocalization M S F h
  change FractionRing.algEquiv S F (algebraMap S (FractionRing S) x) = algebraMap S F x
  exact (FractionRing.algEquiv S F).commutes x

private theorem localizationFieldEquiv_base {R S F : Type*} [CommRing R] [CommRing S]
    [Field F] [Algebra R S] [Algebra R F] [IsFractionRing R F] (M : Submonoid R)
    [IsLocalization M S] (h : M ≤ nonZeroDivisors R) (x : R) :
    localizationFieldEquiv (S := S) (F := F) M h (algebraMap R F x) =
      algebraMap S (FractionRing S) (algebraMap R S x) := by
  letI : Algebra S F :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S F M (nonZeroDivisors R) h
  letI : IsScalarTower R S F :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S F M (nonZeroDivisors R) h
  letI : IsFractionRing S F := IsFractionRing.isFractionRing_of_isLocalization M S F h
  change (FractionRing.algEquiv S F).symm (algebraMap R F x) = _
  rw [IsScalarTower.algebraMap_apply R S F]
  exact (FractionRing.algEquiv S F).symm.commutes (algebraMap R S x)

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev C := WeierstrassInfinityChartAlgebra.Ring W

private theorem affineY_ne_zero : affineY W ≠ 0 := by
  simpa only [affineY, WeierstrassCurve.Affine.CoordinateRing.YClass, map_zero, sub_zero] using
    (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero (W' := W) (0 : Polynomial K))

private theorem chart_isDomain : IsDomain (C W) := by
  letI : IsDomain (ZOverlap W) := Localization.Away.isDomain (affineY_ne_zero W)
  exact Function.Injective.isDomain (toZChart W).toRingHom
    (WeierstrassInfinityChartImage.toZChart_injective W)

attribute [local instance] chart_isDomain

private theorem bracket_ne_zero : bracket W ≠ 0 := by
  intro h
  exact one_ne_zero (by rw [← origin_bracket W, h, map_zero])

private def affineOverlapFractionEquiv : W.FunctionField ≃+* FractionRing (ZOverlap W) :=
  localizationFieldEquiv (Submonoid.powers (affineY W))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (affineY_ne_zero W))

private def infinityOverlapFractionEquiv :
    FractionRing (C W) ≃+* FractionRing (YOverlap W) :=
  localizationFieldEquiv _ (Submonoid.powers_le.mpr (WeierstrassInfinityChartRegular.z_regular W))

private def infinityNeighborhoodFractionEquiv :
    FractionRing (C W) ≃+* FractionRing (Neighborhood W) :=
  localizationFieldEquiv (Submonoid.powers (bracket W))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (bracket_ne_zero W))

private def overlapFractionEquiv : FractionRing (YOverlap W) ≃+* FractionRing (ZOverlap W) :=
  IsFractionRing.ringEquivOfRingEquiv (overlapEquiv W).toRingEquiv

/-- The genuine overlap in the projective plane gives a canonical isomorphism
from the usual Weierstrass function field to the fraction field at infinity. -/
def functionFieldEquiv : W.FunctionField ≃+* FractionRing (Neighborhood W) :=
  (affineOverlapFractionEquiv W).trans
    ((overlapFractionEquiv W).symm.trans
      ((infinityOverlapFractionEquiv W).symm.trans (infinityNeighborhoodFractionEquiv W)))

/-- Restriction of a regular function from the projective Y-chart to the
generic point, expressed in the native Weierstrass function field. -/
def yChartToFunctionField : C W →+* W.FunctionField :=
  (localizationFieldLift (Submonoid.powers (affineY W))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (affineY_ne_zero W))).comp
      (toZChart W).toRingHom

theorem functionFieldEquiv_yChart (x : C W) :
    functionFieldEquiv W (yChartToFunctionField W x) =
      algebraMap (Neighborhood W) (FractionRing (Neighborhood W))
        (algebraMap (C W) (Neighborhood W) x) := by
  have hChart : overlapEquiv W (algebraMap (C W) (YOverlap W) x) = toZChart W x := by
    change toZOverlap W (algebraMap (C W) (YOverlap W) x) = toZChart W x
    unfold toZOverlap
    rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl
  have hA :
      affineOverlapFractionEquiv W (yChartToFunctionField W x) =
        algebraMap (ZOverlap W) (FractionRing (ZOverlap W)) (toZChart W x) := by
    apply (affineOverlapFractionEquiv W).symm.injective
    rw [RingEquiv.symm_apply_apply]
    exact (localizationFieldEquiv_symm_apply
      (Submonoid.powers (affineY W))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (affineY_ne_zero W)) (toZChart W x)).symm
  have hO : overlapFractionEquiv W
      (algebraMap (YOverlap W) (FractionRing (YOverlap W))
        (algebraMap (C W) (YOverlap W) x)) =
      algebraMap (ZOverlap W) (FractionRing (ZOverlap W)) (toZChart W x) := by
    rw [overlapFractionEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact congrArg (algebraMap (ZOverlap W) (FractionRing (ZOverlap W))) hChart
  have hY :
      infinityOverlapFractionEquiv W (algebraMap (C W) (FractionRing (C W)) x) =
        algebraMap (YOverlap W) (FractionRing (YOverlap W))
          (algebraMap (C W) (YOverlap W) x) :=
    localizationFieldEquiv_base _ _ x
  change infinityNeighborhoodFractionEquiv W ((infinityOverlapFractionEquiv W).symm
    ((overlapFractionEquiv W).symm (affineOverlapFractionEquiv W (yChartToFunctionField W x)))) = _
  rw [hA, ← hO, RingEquiv.symm_apply_apply, ← hY, RingEquiv.symm_apply_apply]
  exact localizationFieldEquiv_base _ _ x

end

end ManuscriptAudit.WeierstrassInfinityFunctionField

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityFunctionField.functionFieldEquiv,
      ``ManuscriptAudit.WeierstrassInfinityFunctionField.functionFieldEquiv_yChart] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
