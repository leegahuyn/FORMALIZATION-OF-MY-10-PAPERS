import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.CubicTriplingCoordinates

/-! Secant and tangent steps on the normalized coordinates used for centered cubics. -/

namespace ManuscriptAudit.CubicNormalizedCoordinates

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicTriplingCoordinates

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

def secant (u₁ v₁ u₂ v₂ : K) : K := (v₁ - v₂) / (u₁ - u₂)

def tangent (A t u v : K) : K := 3 * t * u ^ 2 / (2 * (t + A) * v)

def nextX (A t u₁ u₂ m : K) : K := (t + A) / t * m ^ 2 - u₁ - u₂

def nextY (u₁ v₁ u₃ m : K) : K := m * (u₁ - u₃) - v₁

private theorem abscissa_formula {A x y : K} (hx : x ≠ 0) (he : y ^ 2 = x ^ 3 + A)
    (u₁ u₂ m : K) :
    ((y / x) * m) ^ 2 - x * u₁ - x * u₂ = x * nextX A (x ^ 3) u₁ u₂ m := by
  unfold nextX
  rw [mul_pow, div_pow, he]
  field_simp [hx] <;> ring

private theorem ordinate_formula {x y : K} (hx : x ≠ 0) (u₁ v₁ u₃ m : K) :
    (y / x) * m * (x * u₁ - x * u₃) - y * v₁ = y * nextY u₁ v₁ u₃ m := by
  unfold nextY
  field_simp [hx] <;> ring

set_option maxHeartbeats 600000 in
/-- The native sum on the secant domain is computed using only the normalized factors. -/
theorem add_of_abscissa_ne {A x y u₁ v₁ u₂ v₂ : K}
    (hx : x ≠ 0) (he : y ^ 2 = x ^ 3 + A) (hu : u₁ ≠ u₂)
    (h₁ : (Curve A).Nonsingular (x * u₁) (y * v₁))
    (h₂ : (Curve A).Nonsingular (x * u₂) (y * v₂)) :
    let m := secant u₁ v₁ u₂ v₂
    let u := nextX A (x ^ 3) u₁ u₂ m
    let v := nextY u₁ v₁ u m
    ∃ h : (Curve A).Nonsingular (x * u) (y * v),
      (Affine.Point.some (x * u₁) (y * v₁) h₁ : (Curve A).Point) +
        Affine.Point.some (x * u₂) (y * v₂) h₂ = Affine.Point.some (x * u) (y * v) h := by
  let W := Curve A
  let m := secant u₁ v₁ u₂ v₂
  let u := nextX A (x ^ 3) u₁ u₂ m
  let v := nextY u₁ v₁ u m
  have hu' : x * u₁ ≠ x * u₂ := fun h => hu (mul_left_cancel₀ hx h)
  let q := W.slope (x * u₁) (x * u₂) (y * v₁) (y * v₂)
  have hq : q = (y / x) * m := by
    change W.slope (x * u₁) (x * u₂) (y * v₁) (y * v₂) = _
    rw [Affine.slope_of_X_ne hu']
    unfold m secant
    field_simp [hx, sub_ne_zero.mpr hu, sub_ne_zero.mpr hu'] <;> ring
  have hX : W.addX (x * u₁) (x * u₂) q = x * u := by
    rw [addX_eq, hq]
    exact abscissa_formula hx he u₁ u₂ m
  have hY : W.addY (x * u₁) (x * u₂) (y * v₁) q = y * v := by
    rw [addY_eq, hX, hq]
    exact ordinate_formula hx u₁ v₁ u m
  have hQ : W.Nonsingular (W.addX (x * u₁) (x * u₂) q)
      (W.addY (x * u₁) (x * u₂) (y * v₁) q) :=
    Affine.nonsingular_add h₁ h₂ (fun h => hu' h.1)
  refine ⟨by simpa only [hX, hY] using hQ, ?_⟩
  rw [Affine.Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hu', Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

set_option maxHeartbeats 600000 in
/-- The native double on the tangent domain is computed using only the normalized factors. -/
theorem double_some {A x y u v : K} (h₂ : (2 : K) ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (he : y ^ 2 = x ^ 3 + A) (hv : v ≠ 0)
    (hP : (Curve A).Nonsingular (x * u) (y * v)) :
    let m := tangent A (x ^ 3) u v
    let u' := nextX A (x ^ 3) u u m
    let v' := nextY u v u' m
    ∃ h : (Curve A).Nonsingular (x * u') (y * v'),
      (2 : ℕ) • (Affine.Point.some (x * u) (y * v) hP : (Curve A).Point) =
        Affine.Point.some (x * u') (y * v') h := by
  let W := Curve A
  let m := tangent A (x ^ 3) u v
  let u' := nextX A (x ^ 3) u u m
  let v' := nextY u v u' m
  have hy' : y * v ≠ W.negY (x * u) (y * v) := by
    change y * v ≠ (Curve A).negY (x * u) (y * v)
    rw [CubicTriplingCoordinates.negY_eq]
    intro h
    exact (mul_ne_zero h₂ (mul_ne_zero hy hv)) (by linear_combination h)
  let q := W.slope (x * u) (x * u) (y * v) (y * v)
  have hq₁ : q = (3 * (x * u) ^ 2) / (2 * (y * v)) := by
    change W.slope (x * u) (x * u) (y * v) (y * v) = _
    rw [Affine.slope_of_Y_ne rfl hy', CubicTriplingCoordinates.negY_eq, sub_neg_eq_add, ← two_mul]
    simp [W, Curve, CubicAffine, shortCubic]
  have hq : q = (y / x) * m := by
    rw [hq₁]
    unfold m tangent
    rw [← he]
    field_simp [h₂, hx, hy, hv] <;> ring
  have hX : W.addX (x * u) (x * u) q = x * u' := by
    rw [addX_eq, hq]
    exact abscissa_formula hx he u u m
  have hY : W.addY (x * u) (x * u) (y * v) q = y * v' := by
    rw [addY_eq, hX, hq]
    exact ordinate_formula hx u v u' m
  have hQ : W.Nonsingular (W.addX (x * u) (x * u) q) (W.addY (x * u) (x * u) (y * v) q) :=
    Affine.nonsingular_add hP hP (fun h => hy' h.2)
  refine ⟨by simpa only [hX, hY] using hQ, ?_⟩
  rw [two_nsmul, Affine.Point.add_of_Y_ne hy', Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

end
end ManuscriptAudit.CubicNormalizedCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicNormalizedCoordinates.add_of_abscissa_ne,
      ``ManuscriptAudit.CubicNormalizedCoordinates.double_some] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
