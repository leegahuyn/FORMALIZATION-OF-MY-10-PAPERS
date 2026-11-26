import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartImmersion
import PrimalitySheafVerification.ManuscriptAudit.NodalAwayNormalization

/-! On the overlap of the projective nodal charts the normalization parameter is
invertible, as is its distance from the two branches over the node. -/

namespace ManuscriptAudit.NodalYChartOverlap

open Polynomial
open NodalYChartImmersion (yEquation yCoordinateRing xCoeff zCoeff yRing_linear_relation)

noncomputable section

universe u

variable (K : Type u) [Field K]

abbrev parameterRing := Localization.Away (NodalConductor.y K)
abbrev overlapRing := Localization.Away (xCoeff K)

def t : parameterRing K := algebraMap (Polynomial K) (parameterRing K) X
def denominatorInv : parameterRing K :=
  IsLocalization.Away.invSelf (NodalConductor.y K)
def tInv : parameterRing K := (t K ^ 2 - 1) * denominatorInv K

def x : overlapRing K := algebraMap (yCoordinateRing K) (overlapRing K) (xCoeff K)
def z : overlapRing K := algebraMap (yCoordinateRing K) (overlapRing K) (zCoeff K)
def xInv : overlapRing K := IsLocalization.Away.invSelf (xCoeff K)

theorem denominator_image :
    algebraMap (Polynomial K) (parameterRing K) (NodalConductor.y K) =
      t K * (t K ^ 2 - 1) := by
  let f : Polynomial K →+* parameterRing K := algebraMap _ _
  change f ((X ^ 2 - 1) * X) = f X * (f X ^ 2 - 1)
  calc
    _ = f (X ^ 2 - 1) * f X := f.map_mul _ _
    _ = _ := by rw [f.map_sub, map_pow f, f.map_one, mul_comm]

theorem denominator_mul_inv : t K * (t K ^ 2 - 1) * denominatorInv K = 1 := by
  rw [← denominator_image]
  exact IsLocalization.Away.mul_invSelf (NodalConductor.y K)

theorem t_mul_inv : t K * tInv K = 1 := by
  unfold tInv
  rw [← mul_assoc]
  exact denominator_mul_inv K

theorem x_mul_inv : x K * xInv K = 1 :=
  IsLocalization.Away.mul_invSelf (xCoeff K)

private theorem inverse_unique {R : Type*} [CommRing R] {a b c : R}
    (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  calc
    b = b * (a * c) := by rw [hc, mul_one]
    _ = (a * b) * c := by ring
    _ = c := by rw [hb, one_mul]

private theorem unit_of_inverse {R : Type*} [CommRing R] {a b : R}
    (h : a * b = 1) : IsUnit a :=
  ⟨{ val := a, inv := b, val_inv := h, inv_val := (mul_comm b a).trans h }, rfl⟩

private def yPolynomialAtParameter : Polynomial K →ₐ[K] parameterRing K :=
  aeval (tInv K)

private theorem yPolynomialAtParameter_X : yPolynomialAtParameter K X = tInv K :=
  aeval_X (tInv K)

private theorem toParameter_relation :
    (yEquation K).eval₂ (yPolynomialAtParameter K) (denominatorInv K) = 0 := by
  unfold yEquation
  rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
  simp only [map_sub, map_pow, map_one]
  apply sub_eq_zero.mpr
  change (1 - yPolynomialAtParameter K X ^ 2) * denominatorInv K =
    yPolynomialAtParameter K X ^ 3
  rw [yPolynomialAtParameter_X]
  have hinv : t K * tInv K = 1 := t_mul_inv K
  have hscale : 1 - tInv K ^ 2 = (t K ^ 2 - 1) * tInv K ^ 2 := by
    calc
      _ = (t K * tInv K) ^ 2 - tInv K ^ 2 := by rw [hinv, one_pow]
      _ = _ := by ring
  rw [hscale, show (t K ^ 2 - 1) * tInv K ^ 2 * denominatorInv K =
      ((t K ^ 2 - 1) * denominatorInv K) * tInv K ^ 2 by ring]
  rw [← tInv]
  ring

def yToParameter : yCoordinateRing K →ₐ[K] parameterRing K :=
  AdjoinRoot.liftAlgHom (yEquation K) (yPolynomialAtParameter K) (denominatorInv K)
    (toParameter_relation K)

theorem yToParameter_x : yToParameter K (xCoeff K) = tInv K :=
  (AdjoinRoot.liftAlgHom_of (yEquation K) (yPolynomialAtParameter K) (denominatorInv K)
    (toParameter_relation K) (X : Polynomial K)).trans (yPolynomialAtParameter_X K)

theorem yToParameter_z : yToParameter K (zCoeff K) = denominatorInv K := by
  unfold yToParameter zCoeff
  apply AdjoinRoot.liftAlgHom_root

def toParameter : overlapRing K →ₐ[K] parameterRing K :=
  IsLocalization.Away.liftAlgHom (xCoeff K) (f := yToParameter K)
    (by rw [yToParameter_x]; exact unit_of_inverse (by rw [mul_comm]; exact t_mul_inv K))

theorem toParameter_x : toParameter K (x K) = tInv K := by
  unfold toParameter x
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact yToParameter_x K

theorem toParameter_z : toParameter K (z K) = denominatorInv K := by
  unfold toParameter z
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact yToParameter_z K

theorem toParameter_xInv : toParameter K (xInv K) = t K := by
  have h := congrArg (toParameter K) (x_mul_inv K)
  rw [map_mul, map_one, toParameter_x] at h
  exact inverse_unique h (by rw [mul_comm]; exact t_mul_inv K)

private theorem overlap_relation : (1 - x K ^ 2) * z K = x K ^ 3 := by
  have h := congrArg (algebraMap (yCoordinateRing K) (overlapRing K)) (yRing_linear_relation K)
  simpa only [map_sub, map_mul, map_one, map_pow, x, z] using h

private theorem parameter_denominator_at_xInv :
    xInv K * (xInv K ^ 2 - 1) * z K = 1 := by
  have hi : x K * xInv K = 1 := x_mul_inv K
  have hfactor : xInv K ^ 2 - 1 = xInv K ^ 2 * (1 - x K ^ 2) := by
    calc
      _ = xInv K ^ 2 - (x K * xInv K) ^ 2 := by rw [hi, one_pow]
      _ = _ := by ring
  calc
    _ = xInv K ^ 3 * ((1 - x K ^ 2) * z K) := by rw [hfactor]; ring
    _ = (x K * xInv K) ^ 3 := by rw [overlap_relation]; ring
    _ = 1 := by rw [hi, one_pow]

private theorem aeval_xInv_denominator :
    aeval (R := K) (xInv K) (NodalConductor.y K) =
      xInv K * (xInv K ^ 2 - 1) := by
  unfold NodalConductor.y NodalConductor.x
  rw [map_mul, map_sub, map_pow, map_one, aeval_X, mul_comm]

def fromParameter : parameterRing K →ₐ[K] overlapRing K :=
  IsLocalization.Away.liftAlgHom (NodalConductor.y K) (f := aeval (xInv K))
    (by rw [aeval_xInv_denominator]; exact unit_of_inverse (parameter_denominator_at_xInv K))

theorem fromParameter_t : fromParameter K (t K) = xInv K := by
  unfold fromParameter t
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact aeval_X (xInv K)

theorem fromParameter_tInv : fromParameter K (tInv K) = x K := by
  have h := congrArg (fromParameter K) (t_mul_inv K)
  rw [map_mul, map_one, fromParameter_t] at h
  exact inverse_unique h (by rw [mul_comm]; exact x_mul_inv K)

theorem fromParameter_denominatorInv : fromParameter K (denominatorInv K) = z K := by
  have h := congrArg (fromParameter K) (denominator_mul_inv K)
  rw [map_mul, map_mul, map_sub, map_pow, map_one, fromParameter_t] at h
  exact inverse_unique h (parameter_denominator_at_xInv K)

/-- The Y-chart overlap is the polynomial parameter line with t(t²−1) inverted. -/
def overlapEquiv : overlapRing K ≃ₐ[K] parameterRing K := by
  refine AlgEquiv.ofAlgHom (toParameter K) (fromParameter K) ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers (NodalConductor.y K))
    apply Polynomial.algHom_ext
    change toParameter K (fromParameter K (t K)) = t K
    rw [fromParameter_t, toParameter_xInv]
  · apply IsLocalization.algHom_ext (Submonoid.powers (xCoeff K))
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change fromParameter K (toParameter K (x K)) = x K
      rw [toParameter_x, fromParameter_tInv]
    · change fromParameter K (toParameter K (z K)) = z K
      rw [toParameter_z, fromParameter_denominatorInv]

theorem overlapEquiv_x : overlapEquiv K (x K) = tInv K :=
  toParameter_x K

theorem overlapEquiv_z : overlapEquiv K (z K) = denominatorInv K :=
  toParameter_z K

/-- The localizations of the two actual coordinate rings have the same parameter. -/
def zChartOverlapEquiv :
    Localization.Away (NodalAwayNormalization.nodeY K) ≃ₐ[K] overlapRing K :=
  (NodalAwayNormalization.overlapNormalizationEquiv K).trans (overlapEquiv K).symm

end
end ManuscriptAudit.NodalYChartOverlap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalYChartOverlap.yToParameter_x,
      ``ManuscriptAudit.NodalYChartOverlap.yToParameter_z,
      ``ManuscriptAudit.NodalYChartOverlap.overlapEquiv_x,
      ``ManuscriptAudit.NodalYChartOverlap.overlapEquiv_z,
      ``ManuscriptAudit.NodalYChartOverlap.zChartOverlapEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
