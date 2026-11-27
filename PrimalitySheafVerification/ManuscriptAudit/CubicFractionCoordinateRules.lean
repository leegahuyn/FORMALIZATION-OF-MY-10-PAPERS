import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFractionCertificates
import PrimalitySheafVerification.ManuscriptAudit.CubicNormalizedCoordinates

/-! Validated polynomial-fraction steps for the normalized centered cubic formulas. -/

namespace ManuscriptAudit.CubicFractionCoordinateRules

open CubicFractionCertificates CubicNormalizedCoordinates
open Fraction

variable {k : Type*} [CommRing k]

def secantFraction (u₁ v₁ u₂ v₂ : Fraction k) : Fraction k :=
  (v₁ - v₂) / (u₁ - u₂)

def tangentFraction (A : k) (u v : Fraction k) : Fraction k :=
  (scalar 3 * variableX * u ^ 2) / (scalar 2 * (variableX + scalar A) * v)

def xFraction (A : k) (u₁ u₂ m : Fraction k) : Fraction k :=
  (variableX + scalar A) / variableX * m ^ 2 - u₁ - u₂

def yFraction (u₁ v₁ u₃ m : Fraction k) : Fraction k :=
  m * (u₁ - u₃) - v₁

variable {L : Type*} [Field L] [Algebra k L]

private theorem valid_scalar (a : k) (t : L) : (scalar a).ValidAt t :=
  valid_polynomial _ _

private theorem valid_variable (t : L) : (variableX (k := k)).ValidAt t :=
  valid_polynomial _ _

private theorem evaluate_t_add (A : k) (t : L) :
    ((variableX (k := k)) + scalar A).evaluate t = t + algebraMap k L A := by
  rw [evaluate_add (valid_variable t) (valid_scalar A t), evaluate_variableX, evaluate_scalar]

theorem secant_check {t : L} {u₁ v₁ u₂ v₂ : Fraction k}
    (hu₁ : u₁.ValidAt t) (hv₁ : v₁.ValidAt t) (hu₂ : u₂.ValidAt t) (hv₂ : v₂.ValidAt t)
    (hd : u₁.evaluate t ≠ u₂.evaluate t) :
    (secantFraction u₁ v₁ u₂ v₂).ValidAt t ∧
      (secantFraction u₁ v₁ u₂ v₂).evaluate t =
        secant (u₁.evaluate t) (v₁.evaluate t) (u₂.evaluate t) (v₂.evaluate t) := by
  unfold secantFraction secant
  have hD : (u₁ - u₂).evaluate t ≠ 0 := by
    rw [evaluate_sub hu₁ hu₂]
    exact sub_ne_zero.mpr hd
  refine ⟨valid_div (valid_sub hv₁ hv₂) hD, ?_⟩
  rw [evaluate_div, evaluate_sub hv₁ hv₂, evaluate_sub hu₁ hu₂]

theorem tangent_check {t : L} {A : k} {u v : Fraction k}
    (hu : u.ValidAt t) (h₂ : (2 : L) ≠ 0) (hs : t + algebraMap k L A ≠ 0)
    (hV : v.evaluate t ≠ 0) :
    (tangentFraction A u v).ValidAt t ∧
      (tangentFraction A u v).evaluate t =
        tangent (algebraMap k L A) t (u.evaluate t) (v.evaluate t) := by
  unfold tangentFraction tangent
  have hD : (scalar 2 * (variableX + scalar A) * v).evaluate t ≠ 0 := by
    rw [evaluate_mul, evaluate_mul, evaluate_scalar, evaluate_t_add, map_ofNat]
    exact mul_ne_zero (mul_ne_zero h₂ hs) hV
  refine ⟨valid_div (valid_mul (valid_mul (valid_scalar 3 t) (valid_variable t)) (valid_pow hu 2)) hD, ?_⟩
  rw [evaluate_div, evaluate_mul, evaluate_mul, evaluate_pow, evaluate_mul, evaluate_mul,
    evaluate_t_add, evaluate_variableX, evaluate_scalar, evaluate_scalar, map_ofNat, map_ofNat]

theorem x_check {t : L} {A : k} {u₁ u₂ m : Fraction k}
    (ht : t ≠ 0) (hu₁ : u₁.ValidAt t) (hu₂ : u₂.ValidAt t) (hm : m.ValidAt t) :
    (xFraction A u₁ u₂ m).ValidAt t ∧
      (xFraction A u₁ u₂ m).evaluate t =
        nextX (algebraMap k L A) t (u₁.evaluate t) (u₂.evaluate t) (m.evaluate t) := by
  unfold xFraction nextX
  have hRatio : (((variableX (k := k)) + scalar A) / variableX).ValidAt t :=
    valid_div (valid_add (valid_variable t) (valid_scalar A t)) (by simpa only [evaluate_variableX] using ht)
  have hM := valid_mul hRatio (valid_pow hm 2)
  refine ⟨valid_sub (valid_sub hM hu₁) hu₂, ?_⟩
  rw [evaluate_sub (valid_sub hM hu₁) hu₂, evaluate_sub hM hu₁, evaluate_mul,
    evaluate_div, evaluate_t_add, evaluate_variableX, evaluate_pow]

theorem y_check {t : L} {u₁ v₁ u₃ m : Fraction k}
    (hu₁ : u₁.ValidAt t) (hv₁ : v₁.ValidAt t) (hu₃ : u₃.ValidAt t) (hm : m.ValidAt t) :
    (yFraction u₁ v₁ u₃ m).ValidAt t ∧
      (yFraction u₁ v₁ u₃ m).evaluate t =
        nextY (u₁.evaluate t) (v₁.evaluate t) (u₃.evaluate t) (m.evaluate t) := by
  unfold yFraction nextY
  have hM := valid_mul hm (valid_sub hu₁ hu₃)
  refine ⟨valid_sub hM hv₁, ?_⟩
  rw [evaluate_sub hM hv₁, evaluate_mul, evaluate_sub hu₁ hu₃]

end ManuscriptAudit.CubicFractionCoordinateRules

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFractionCoordinateRules.secant_check,
      ``ManuscriptAudit.CubicFractionCoordinateRules.tangent_check,
      ``ManuscriptAudit.CubicFractionCoordinateRules.x_check,
      ``ManuscriptAudit.CubicFractionCoordinateRules.y_check] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
