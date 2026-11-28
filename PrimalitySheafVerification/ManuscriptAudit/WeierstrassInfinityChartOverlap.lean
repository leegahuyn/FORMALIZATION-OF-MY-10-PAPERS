import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartCoordinates

/-! The coordinate-ring isomorphism on the common part of the Y=1 and Z=1 charts. -/

namespace ManuscriptAudit.WeierstrassInfinityChartOverlap

open Polynomial WeierstrassCurve.Affine
open WeierstrassInfinityChartCoordinates
open scoped Polynomial.Bivariate

universe u

noncomputable section

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

abbrev A := W.CoordinateRing
abbrev C₀ := WeierstrassInfinityChartAlgebra.Ring W
abbrev ZOverlap := Localization.Away (affineY W)
abbrev YOverlap := Localization.Away (WeierstrassInfinityChartAlgebra.z W)

def zx : ZOverlap W := algebraMap (A W) (ZOverlap W) (affineX W)
def zy : ZOverlap W := algebraMap (A W) (ZOverlap W) (affineY W)
def zInv : ZOverlap W := IsLocalization.Away.invSelf (affineY W)

def yx : YOverlap W := algebraMap (C₀ W) (YOverlap W) (WeierstrassInfinityChartAlgebra.x W)
def yz : YOverlap W := algebraMap (C₀ W) (YOverlap W) (WeierstrassInfinityChartAlgebra.z W)
def yInv : YOverlap W := IsLocalization.Away.invSelf (WeierstrassInfinityChartAlgebra.z W)

theorem zy_mul_zInv : zy W * zInv W = 1 := IsLocalization.Away.mul_invSelf (affineY W)
theorem yz_mul_yInv : yz W * yInv W = 1 :=
  IsLocalization.Away.mul_invSelf (WeierstrassInfinityChartAlgebra.z W)

private theorem inverse_unique {R : Type*} [CommRing R] {a b c : R}
    (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  calc
    b = b * (a * c) := by rw [hc, mul_one]
    _ = (a * b) * c := by ac_rfl
    _ = c := by rw [hb, one_mul]

private theorem unit_of_inverse {R : Type*} [CommRing R] {a b : R}
    (h : a * b = 1) : IsUnit a :=
  ⟨{ val := a, inv := b, val_inv := h, inv_val := (mul_comm b a).trans h }, rfl⟩

private theorem localized_affine_relation : affineEquation W (zx W) (zy W) = 0 := by
  have h := congrArg (algebraMap (A W) (ZOverlap W)) (affine_relation W)
  simpa only [affineEquation, zx, zy, map_add, map_sub, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply] using h

private theorem localized_infinity_relation : infinityEquation W (yx W) (yz W) = 0 := by
  have h := congrArg (algebraMap (C₀ W) (YOverlap W)) (infinity_relation W)
  simpa only [infinityEquation, yx, yz, map_add, map_sub, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply] using h

private theorem toZ_relation : (WeierstrassInfinityChartAlgebra.equation W).eval₂
    (Polynomial.aeval (R := K) (zx W * zInv W)).toRingHom (zInv W) = 0 := by
  rw [eval_infinityEquation]
  exact affine_to_infinity W _ _ _ (localized_affine_relation W) (zy_mul_zInv W)

private theorem toY_relation : W.polynomial.eval₂
    (Polynomial.aeval (R := K) (yx W * yInv W)).toRingHom (yInv W) = 0 := by
  rw [eval_affineEquation]
  exact infinity_to_affine W _ _ _ (localized_infinity_relation W) (yz_mul_yInv W)

def toZChart : C₀ W →ₐ[K] ZOverlap W :=
  AdjoinRoot.liftAlgHom (WeierstrassInfinityChartAlgebra.equation W)
    (Polynomial.aeval (zx W * zInv W)) (zInv W) (toZ_relation W)

def toYChart : A W →ₐ[K] YOverlap W :=
  AdjoinRoot.liftAlgHom W.polynomial (Polynomial.aeval (yx W * yInv W)) (yInv W) (toY_relation W)

theorem toZChart_x :
    toZChart W (WeierstrassInfinityChartAlgebra.x W) = zx W * zInv W :=
  (AdjoinRoot.liftAlgHom_of (WeierstrassInfinityChartAlgebra.equation W)
    (Polynomial.aeval (R := K) (zx W * zInv W))
    (zInv W) (toZ_relation W) X).trans (Polynomial.aeval_X _)

theorem toZChart_z : toZChart W (WeierstrassInfinityChartAlgebra.z W) = zInv W :=
  AdjoinRoot.liftAlgHom_root (WeierstrassInfinityChartAlgebra.equation W)
    (Polynomial.aeval (R := K) (zx W * zInv W)) (zInv W) (toZ_relation W)

theorem toYChart_x : toYChart W (affineX W) = yx W * yInv W :=
  (AdjoinRoot.liftAlgHom_of W.polynomial (Polynomial.aeval (R := K) (yx W * yInv W))
    (yInv W) (toY_relation W) X).trans (Polynomial.aeval_X _)

theorem toYChart_y : toYChart W (affineY W) = yInv W :=
  AdjoinRoot.liftAlgHom_root W.polynomial (Polynomial.aeval (R := K) (yx W * yInv W))
    (yInv W) (toY_relation W)

def toZOverlap : YOverlap W →ₐ[K] ZOverlap W :=
  IsLocalization.Away.liftAlgHom (WeierstrassInfinityChartAlgebra.z W) (f := toZChart W)
    (by rw [toZChart_z]; exact unit_of_inverse ((mul_comm _ _).trans (zy_mul_zInv W)))

def toYOverlap : ZOverlap W →ₐ[K] YOverlap W :=
  IsLocalization.Away.liftAlgHom (affineY W) (f := toYChart W)
    (by rw [toYChart_y]; exact unit_of_inverse ((mul_comm _ _).trans (yz_mul_yInv W)))

theorem toZOverlap_x : toZOverlap W (yx W) = zx W * zInv W := by
  unfold toZOverlap yx
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact toZChart_x W

theorem toZOverlap_z : toZOverlap W (yz W) = zInv W := by
  unfold toZOverlap yz
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact toZChart_z W

theorem toYOverlap_x : toYOverlap W (zx W) = yx W * yInv W := by
  unfold toYOverlap zx
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact toYChart_x W

theorem toYOverlap_y : toYOverlap W (zy W) = yInv W := by
  unfold toYOverlap zy
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact toYChart_y W

theorem toZOverlap_inv : toZOverlap W (yInv W) = zy W := by
  have h := congrArg (toZOverlap W) (yz_mul_yInv W)
  rw [map_mul, map_one, toZOverlap_z] at h
  exact inverse_unique h ((mul_comm _ _).trans (zy_mul_zInv W))

theorem toYOverlap_inv : toYOverlap W (zInv W) = yz W := by
  have h := congrArg (toYOverlap W) (zy_mul_zInv W)
  rw [map_mul, map_one, toYOverlap_y] at h
  exact inverse_unique h ((mul_comm _ _).trans (yz_mul_yInv W))

/-- The common open charts have isomorphic coordinate rings by the projective rescalings. -/
def overlapEquiv : YOverlap W ≃ₐ[K] ZOverlap W := by
  refine AlgEquiv.ofAlgHom (toZOverlap W) (toYOverlap W) ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers (affineY W))
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change toZOverlap W (toYOverlap W (zx W)) = zx W
      rw [toYOverlap_x, map_mul, toZOverlap_x, toZOverlap_inv, mul_assoc,
        mul_comm (zInv W) (zy W), zy_mul_zInv, mul_one]
    · change toZOverlap W (toYOverlap W (zy W)) = zy W
      rw [toYOverlap_y, toZOverlap_inv]
  · apply IsLocalization.algHom_ext (Submonoid.powers (WeierstrassInfinityChartAlgebra.z W))
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change toYOverlap W (toZOverlap W (yx W)) = yx W
      rw [toZOverlap_x, map_mul, toYOverlap_x, toYOverlap_inv, mul_assoc,
        mul_comm (yInv W) (yz W), yz_mul_yInv, mul_one]
    · change toYOverlap W (toZOverlap W (yz W)) = yz W
      rw [toZOverlap_z, toYOverlap_inv]

end

end ManuscriptAudit.WeierstrassInfinityChartOverlap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityChartOverlap.toZChart_x,
      ``ManuscriptAudit.WeierstrassInfinityChartOverlap.toZChart_z,
      ``ManuscriptAudit.WeierstrassInfinityChartOverlap.toYChart_x,
      ``ManuscriptAudit.WeierstrassInfinityChartOverlap.toYChart_y,
      ``ManuscriptAudit.WeierstrassInfinityChartOverlap.overlapEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
