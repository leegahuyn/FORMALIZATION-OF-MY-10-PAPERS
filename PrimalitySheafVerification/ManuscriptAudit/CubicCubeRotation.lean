import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! The native additive cube-root rotation on the centered Weierstrass cubic. -/

namespace ManuscriptAudit.CubicCubeRotation

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A z : K}

private theorem negY_eq (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

private theorem scalar_ne_zero (hz : z ^ 3 = 1) : z ≠ 0 := by
  intro h
  simpa [h] using hz

private theorem slope_rotate (hz : z ^ 3 = 1) (x₁ x₂ y₁ y₂ : K) :
    (Curve A).slope (z * x₁) (z * x₂) y₁ y₂ = z ^ 2 * (Curve A).slope x₁ x₂ y₁ y₂ := by
  let W := Curve A
  change W.slope (z * x₁) (z * x₂) y₁ y₂ = z ^ 2 * W.slope x₁ x₂ y₁ y₂
  by_cases hX : x₁ = x₂
  · have hXZ : z * x₁ = z * x₂ := congrArg (fun x => z * x) hX
    by_cases hY : y₁ = W.negY x₂ y₂
    · have hYZ : y₁ = W.negY (z * x₂) y₂ := by simpa only [W, negY_eq] using hY
      rw [Affine.slope_of_Y_eq hXZ hYZ, Affine.slope_of_Y_eq hX hY, mul_zero]
    · have hYZ : y₁ ≠ W.negY (z * x₂) y₂ := by simpa only [W, negY_eq] using hY
      rw [Affine.slope_of_Y_ne hXZ hYZ, Affine.slope_of_Y_ne hX hY]
      simp only [W, Curve, CubicAffine, shortCubic, negY_eq, neg_zero, mul_zero, zero_mul, add_zero,
        sub_zero]
      rw [← mul_div_assoc]
      congr 1
      ring
  · have hz₀ := scalar_ne_zero hz
    have hXZ : z * x₁ ≠ z * x₂ := fun he => hX (mul_left_cancel₀ hz₀ he)
    rw [Affine.slope_of_X_ne hXZ, Affine.slope_of_X_ne hX, ← mul_sub]
    apply (div_eq_iff (mul_ne_zero hz₀ (sub_ne_zero.mpr hX))).mpr
    calc
      _ = z ^ 3 * (((y₁ - y₂) / (x₁ - x₂)) * (x₁ - x₂)) := by ring
      _ = _ := by rw [hz, one_mul, div_mul_cancel₀ _ (sub_ne_zero.mpr hX)]

private theorem addX_rotate (hz : z ^ 3 = 1) (x₁ x₂ ell : K) :
    (Curve A).addX (z * x₁) (z * x₂) (z ^ 2 * ell) = z * (Curve A).addX x₁ x₂ ell := by
  have hz₄ : z ^ 4 = z := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hz, pow_one, one_mul]
  simp only [Affine.addX, Curve, CubicAffine, shortCubic, zero_mul, add_zero, sub_zero]
  rw [mul_pow, ← pow_mul, show (2 : ℕ) * 2 = 4 by decide, hz₄]
  ring

private theorem addY_rotate (hz : z ^ 3 = 1) (x₁ x₂ y₁ ell : K) :
    (Curve A).addY (z * x₁) (z * x₂) y₁ (z ^ 2 * ell) = (Curve A).addY x₁ x₂ y₁ ell := by
  let X := (Curve A).addX x₁ x₂ ell
  simp only [Affine.addY, negY_eq, Affine.negAddY, addX_rotate hz]
  change -(z ^ 2 * ell * (z * X - z * x₁) + y₁) = -(ell * (X - x₁) + y₁)
  calc
    _ = -(z ^ 3 * (ell * (X - x₁)) + y₁) := by ring
    _ = _ := by rw [hz, one_mul]

private theorem rotated_nonsingular (hz : z ^ 3 = 1)
    (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) {x y : K} (h : (Curve A).Nonsingular x y) :
    (Curve A).Nonsingular (z * x) y := by
  apply (nonsingular_iff hΔ _ _).mpr
  rw [mul_pow, hz, one_mul]
  exact (nonsingular_iff hΔ x y).mp h

private def rotatePoint (z : K) (hz : z ^ 3 = 1) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) :
    (Curve A).Point → (Curve A).Point
  | .zero => 0
  | .some x y h => .some (z * x) y (rotated_nonsingular hz hΔ h)

private theorem rotatePoint_add (hz : z ^ 3 = 1) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (P Q : (Curve A).Point) :
    rotatePoint z hz hΔ (P + Q) = rotatePoint z hz hΔ P + rotatePoint z hz hΔ Q := by
  cases P with
  | zero =>
    change rotatePoint z hz hΔ (0 + Q) = 0 + rotatePoint z hz hΔ Q
    rw [zero_add, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change rotatePoint z hz hΔ (Affine.Point.some x₁ y₁ h₁ + 0) =
        rotatePoint z hz hΔ (Affine.Point.some x₁ y₁ h₁) + 0
      rw [add_zero, add_zero]
    | some x₂ y₂ h₂ =>
      let W := Curve A
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
      · have hxz : z * x₁ = z * x₂ := congrArg (fun x => z * x) hxy.1
        have hyz : y₁ = W.negY (z * x₂) y₂ := by simpa only [W, negY_eq] using hxy.2
        rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        change (0 : W.Point) = .some (z * x₁) y₁ (rotated_nonsingular hz hΔ h₁) +
          .some (z * x₂) y₂ (rotated_nonsingular hz hΔ h₂)
        rw [Affine.Point.add_of_Y_eq hxz hyz]
      · have hxyz : ¬(z * x₁ = z * x₂ ∧ y₁ = W.negY (z * x₂) y₂) := by
          rintro ⟨hx, hy⟩
          exact hxy ⟨mul_left_cancel₀ (scalar_ne_zero hz) hx, by simpa only [W, negY_eq] using hy⟩
        let ell := W.slope x₁ x₂ y₁ y₂
        rw [Affine.Point.add_some hxy]
        change Affine.Point.some (z * W.addX x₁ x₂ ell) (W.addY x₁ x₂ y₁ ell)
            (rotated_nonsingular hz hΔ (Affine.nonsingular_add h₁ h₂ hxy)) =
          .some (z * x₁) y₁ (rotated_nonsingular hz hΔ h₁) +
          .some (z * x₂) y₂ (rotated_nonsingular hz hΔ h₂)
        rw [Affine.Point.add_some hxyz, Affine.Point.some.injEq]
        have hs : W.slope (z * x₁) (z * x₂) y₁ y₂ = z ^ 2 * ell :=
          slope_rotate (A := A) hz x₁ x₂ y₁ y₂
        rw [hs]
        exact ⟨(addX_rotate (A := A) hz x₁ x₂ ell).symm,
          (addY_rotate (A := A) hz x₁ x₂ y₁ ell).symm⟩

/-- Multiplication of abscissas by a cube root of unity on the actual point group. -/
def rotate (z : K) (hz : z ^ 3 = 1) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) :
    (Curve A).Point →+ (Curve A).Point where
  toFun := rotatePoint z hz hΔ
  map_zero' := rfl
  map_add' := rotatePoint_add hz hΔ

theorem rotate_some (hz : z ^ 3 = 1) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) {x y : K}
    (h : (Curve A).Nonsingular x y) :
    rotate z hz hΔ (Affine.Point.some x y h) =
      Affine.Point.some (z * x) y (rotated_nonsingular hz hΔ h) := rfl

theorem rotate_abscissa (hz : z ^ 3 = 1) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (P : (Curve A).Point) : abscissa (rotate z hz hΔ P) = z * abscissa P := by
  cases P with
  | zero =>
    change (0 : K) = z * 0
    rw [mul_zero]
  | some x y h => rfl

theorem rotate_cube (hz : z ^ 3 = 1) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (P : (Curve A).Point) : rotate z hz hΔ (rotate z hz hΔ (rotate z hz hΔ P)) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [rotate_some, Affine.Point.some.injEq, and_true]
    calc
      z * (z * (z * x)) = z ^ 3 * x := by ring
      _ = x := by rw [hz, one_mul]

end
end ManuscriptAudit.CubicCubeRotation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCubeRotation.rotate,
      ``ManuscriptAudit.CubicCubeRotation.rotate_abscissa,
      ``ManuscriptAudit.CubicCubeRotation.rotate_cube] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
