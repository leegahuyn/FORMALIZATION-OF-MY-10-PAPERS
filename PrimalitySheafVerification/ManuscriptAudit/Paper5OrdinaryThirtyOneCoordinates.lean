import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic
import PrimalitySheafVerification.ManuscriptAudit.CubicCertifiedCoordinateSteps
import PrimalitySheafVerification.ManuscriptAudit.CubicPolynomialGuard
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates

/-! The exact finite-domain native coordinates of 1+6ρ in characteristic thirty-one. -/

namespace ManuscriptAudit.Paper5OrdinaryThirtyOneCoordinates

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicFractionCertificates CubicCertifiedCoordinateSteps CubicPolynomialGuard
open Paper5OrdinaryThirtyOneCertificates

noncomputable section

local instance : Fact (Nat.Prime 31) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 31) L] [CharP L 31] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 31) L (1 : ZMod 31)
abbrev Points := (Curve (a L)).Point

theorem numeral_ne_zero (n : ℕ) (h : ¬31 ∣ n) : (n : L) ≠ 0 := by
  rwa [ne_eq, CharP.cast_eq_zero_iff L 31 n]

theorem cube_rotation : (5 : L) ^ 3 = 1 := by
  have h : (31 : L) = 0 := by simpa only [Nat.cast_ofNat] using CharP.cast_eq_zero L 31
  linear_combination (4 : L) * h

theorem rotation_ne_one : (5 : L) ≠ 1 := by
  intro h
  exact numeral_ne_zero L 4 (by decide) (by linear_combination h)

theorem a_ne_zero : a L ≠ 0 := by simp [a]

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero
    (numeral_ne_zero L 2 (by decide)) (numeral_ne_zero L 3 (by decide)) (a_ne_zero L)

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate 5 (cube_rotation L) (discriminant_ne_zero L)

theorem rotation_some {x y : L} (h : (Curve (a L)).Nonsingular x y) :
    ∃ h' : (Curve (a L)).Nonsingular (5 * x) y,
      rotation L (Affine.Point.some x y h) = Affine.Point.some (5 * x) y h' :=
  ⟨_, CubicCubeRotation.rotate_some (cube_rotation L) (discriminant_ne_zero L) h⟩

theorem rotation_sq (P : Points L) : rotation L (rotation L P) = -P - rotation L P := by
  have h := CubicRotationQuadratic.rotate_sum_eq_zero
    (numeral_ne_zero L 2 (by decide)) (numeral_ne_zero L 3 (by decide)) (a_ne_zero L)
    (cube_rotation L) (rotation_ne_one L) (discriminant_ne_zero L) P
  change rotation L (rotation L P) + rotation L P + P = 0 at h
  apply sub_eq_zero.mp
  calc
    _ = rotation L (rotation L P) + rotation L P + P := by abel
    _ = _ := h

set_option maxHeartbeats 1800000 in
theorem computed_some {x y : L} (hP : (Curve (a L)).Nonsingular x y)
    (hxGood : x ∉ Exceptional (L := L) excluded) :
    ∃ h' : (Curve (a L)).Nonsingular (x ^ 31) (y ^ 31),
      (Affine.Point.some x y hP : Points L) +
        (6 : ℕ) • rotation L (Affine.Point.some x y hP) = Affine.Point.some (x ^ 31) (y ^ 31) h' := by
  let t := x ^ 3
  let P : Points L := .some x y hP
  have hGuard (f : (ZMod 31)[X]) (hf : f ∈ excluded) :
      f.eval₂ (algebraMap (ZMod 31) L) t ≠ 0 := evaluate_ne_zero hxGood hf
  have valid (f : Fraction (ZMod 31)) (hf : f.den ∈ excluded) : f.ValidAt t := hGuard _ hf
  have ht : t ≠ 0 := by
    simpa only [eval₂_X] using hGuard X (by simp [excluded])
  have hs : t + 1 ≠ 0 := by
    simpa only [eval₂_add, eval₂_X, eval₂_one] using hGuard (X + 1) (by simp [excluded])
  have hx : x ≠ 0 := fun h => ht (by simp [t, h])
  have he := (nonsingular_iff (discriminant_ne_zero L) x y).mp hP
  have he' : y ^ 2 = t + 1 := by simpa only [t, a, map_one] using he
  have hy : y ≠ 0 := fun h => hs (by simpa only [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] using he'.symm)
  have h₂ : (2 : L) ≠ 0 := numeral_ne_zero L 2 (by decide)
  have hUnit : unit.evaluate t = (1 : L) := by simp [unit]
  have hVUnit : unit.ValidAt t := Fraction.valid_polynomial _ _
  have h₀ : (Curve (a L)).Nonsingular (x * unit.evaluate t) (y * unit.evaluate t) := by
    simpa only [hUnit, mul_one] using hP
  have e₀ : P = Affine.Point.some (x * unit.evaluate t) (y * unit.evaluate t) h₀ := by
    change Affine.Point.some x y hP = _
    rw [Affine.Point.some.injEq]
    simp only [hUnit, mul_one, and_self]
  have hGap (f : Fraction (ZMod 31)) (hf : f.ValidAt t) (hn : (unit - f).num ∈ excluded) :
      unit.evaluate t ≠ f.evaluate t := by
    intro h
    have hz : (unit - f).evaluate t = 0 := by
      rw [Fraction.evaluate_sub hVUnit hf, h, sub_self]
    exact (div_ne_zero (hGuard _ hn) (Fraction.valid_sub hVUnit hf)) hz
  have hU₂ := valid u2 (by simp [excluded])
  have hV₂ := valid v2 (by simp [excluded])
  obtain ⟨hTwo, eTwo⟩ := double_step h₂ hx hy he hVUnit hVUnit
    (valid m2 (by simp [excluded])) hU₂ hV₂ (by rw [hUnit]; exact one_ne_zero)
    slope_two x_two y_two h₀
  have e₂ : (2 : ℕ) • P = Affine.Point.some (x * u2.evaluate t) (y * v2.evaluate t) hTwo := by
    rw [e₀]
    exact eTwo
  have hU₃ := valid u3 (by simp [excluded])
  have hV₃ := valid v3 (by simp [excluded])
  obtain ⟨hThree, eThree⟩ := add_step hx he hVUnit hVUnit hU₂ hV₂
    (valid m3 (by simp [excluded])) hU₃ hV₃ (hGap u2 hU₂ (by simp [excluded]))
    slope_three x_three y_three h₀ hTwo
  have e₃ : (3 : ℕ) • P = Affine.Point.some (x * u3.evaluate t) (y * v3.evaluate t) hThree := by
    rw [show (3 : ℕ) = 1 + 2 by decide, add_nsmul, one_nsmul, e₂, e₀]
    exact eThree
  have hV₃ne : v3.evaluate t ≠ 0 := div_ne_zero (hGuard v3.num (by simp [excluded])) hV₃
  have hU₆ := valid u6 (by simp [excluded])
  have hV₆ := valid v6 (by simp [excluded])
  obtain ⟨hSix, eSix⟩ := double_step h₂ hx hy he hU₃ hV₃
    (valid m6 (by simp [excluded])) hU₆ hV₆ hV₃ne slope_six x_six y_six hThree
  have e₆ : (6 : ℕ) • P = Affine.Point.some (x * u6.evaluate t) (y * v6.evaluate t) hSix := by
    rw [show (6 : ℕ) = 2 * 3 by decide, mul_smul, e₃]
    exact eSix
  obtain ⟨hR, eR⟩ := rotation_some L hSix
  have hRotX : x * rotatedSixX.evaluate t = 5 * (x * u6.evaluate t) := by
    rw [rotatedSixX, Fraction.evaluate_mul, Fraction.evaluate_scalar, map_ofNat]
    ring
  have hRot : (Curve (a L)).Nonsingular (x * rotatedSixX.evaluate t) (y * v6.evaluate t) := by
    simpa only [hRotX] using hR
  have eRot : rotation L (Affine.Point.some (x * u6.evaluate t) (y * v6.evaluate t) hSix) =
      Affine.Point.some (x * rotatedSixX.evaluate t) (y * v6.evaluate t) hRot := by
    refine eR.trans ?_
    rw [Affine.Point.some.injEq]
    exact ⟨hRotX.symm, rfl⟩
  have hVRot : rotatedSixX.ValidAt t :=
    Fraction.valid_mul (Fraction.valid_polynomial _ _) hU₆
  obtain ⟨hF, eF⟩ := add_step hx he hVUnit hVUnit hVRot hV₆
    (valid mF (by simp [excluded])) (Fraction.valid_polynomial _ _) (Fraction.valid_polynomial _ _)
    (hGap rotatedSixX hVRot (by simp [excluded])) slope_frobenius x_frobenius y_frobenius h₀ hRot
  have hX : x * frobeniusX.evaluate t = x ^ 31 := by
    simp only [frobeniusX, Fraction.evaluate_polynomial, eval₂_pow, eval₂_X, t]
    ring
  have hY : y * frobeniusY.evaluate t = y ^ 31 := by
    simp only [frobeniusY, Fraction.evaluate_polynomial, eval₂_pow, eval₂_add, eval₂_X, eval₂_one]
    rw [← he']
    ring
  refine ⟨by simpa only [hX, hY] using hF, ?_⟩
  change P + (6 : ℕ) • rotation L P = _
  rw [← map_nsmul (rotation L), e₆, eRot, e₀, eF, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

end
end ManuscriptAudit.Paper5OrdinaryThirtyOneCoordinates

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryThirtyOneCoordinates.computed_some
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
