import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! Coordinate scaling gives an additive equivalence between centered cubics. -/

namespace ManuscriptAudit.CubicPointScaling

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A B u : K}

private theorem negY_eq (C x y : K) : (Curve C).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

private theorem slope_scale (hu : u ≠ 0) (x₁ x₂ y₁ y₂ : K) :
    (Curve B).slope (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂) =
      u * (Curve A).slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · have hx' := congrArg (fun x => u ^ 2 * x) hx
    by_cases hy : y₁ = -(y₂ : K)
    · have hy₁ : y₁ = (Curve A).negY x₂ y₂ := by simpa only [negY_eq] using hy
      have hy₂ : u ^ 3 * y₁ = (Curve B).negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
        rw [negY_eq, hy, mul_neg]
      rw [Affine.slope_of_Y_eq hx hy₁, Affine.slope_of_Y_eq hx' hy₂, mul_zero]
    · have hy₁ : y₁ ≠ (Curve A).negY x₂ y₂ := by simpa only [negY_eq] using hy
      have hy₂ : u ^ 3 * y₁ ≠ (Curve B).negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
        rw [negY_eq, ← mul_neg]
        exact fun he => hy (mul_left_cancel₀ (pow_ne_zero _ hu) he)
      rw [Affine.slope_of_Y_ne hx hy₁, Affine.slope_of_Y_ne hx' hy₂]
      simp only [negY_eq, Curve, CubicAffine, shortCubic, zero_mul, mul_zero, add_zero, sub_zero]
      have hn : 3 * (u ^ 2 * x₁) ^ 2 = u ^ 3 * (u * (3 * x₁ ^ 2)) := by ring
      rw [hn, ← mul_neg, ← mul_sub, mul_div_mul_left _ _ (pow_ne_zero 3 hu), mul_div_assoc]
  · have hx' : u ^ 2 * x₁ ≠ u ^ 2 * x₂ :=
      fun he => hx (mul_left_cancel₀ (pow_ne_zero _ hu) he)
    rw [Affine.slope_of_X_ne hx, Affine.slope_of_X_ne hx', ← mul_sub, ← mul_sub]
    have hn : u ^ 3 * (y₁ - y₂) = u ^ 2 * (u * (y₁ - y₂)) := by ring
    rw [hn, mul_div_mul_left _ _ (pow_ne_zero 2 hu), mul_div_assoc]

private theorem addX_scale (x₁ x₂ ell : K) :
    (Curve B).addX (u ^ 2 * x₁) (u ^ 2 * x₂) (u * ell) =
      u ^ 2 * (Curve A).addX x₁ x₂ ell := by
  simp only [Affine.addX, Curve, CubicAffine, shortCubic, zero_mul, add_zero, sub_zero]
  ring

private theorem addY_scale (x₁ x₂ y ell : K) :
    (Curve B).addY (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y) (u * ell) =
      u ^ 3 * (Curve A).addY x₁ x₂ y ell := by
  simp only [Affine.addY, negY_eq, Affine.negAddY, addX_scale (A := A)]
  ring

theorem scaled_nonsingular (hAB : u ^ 6 * A = B)
    (hB : (shortCubic (0 : K) B).Δ ≠ 0) {x y : K} (h : (Curve A).Nonsingular x y) :
    (Curve B).Nonsingular (u ^ 2 * x) (u ^ 3 * y) := by
  apply (nonsingular_iff hB _ _).mpr
  have hE : y ^ 2 = x ^ 3 + A := by
    simpa [Curve, CubicAffine, shortCubic] using (Affine.equation_iff _ _ _).mp h.1
  linear_combination u ^ 6 * hE + hAB

private def scalePoint (hAB : u ^ 6 * A = B) (hB : (shortCubic (0 : K) B).Δ ≠ 0) :
    (Curve A).Point → (Curve B).Point
  | .zero => 0
  | .some x y h => .some (u ^ 2 * x) (u ^ 3 * y) (scaled_nonsingular hAB hB h)

private theorem scalePoint_add (hu : u ≠ 0)
    (hAB : u ^ 6 * A = B) (hB : (shortCubic (0 : K) B).Δ ≠ 0)
    (P Q : (Curve A).Point) :
    scalePoint hAB hB (P + Q) = scalePoint hAB hB P + scalePoint hAB hB Q := by
  cases P with
  | zero =>
    change scalePoint hAB hB (0 + Q) = 0 + scalePoint hAB hB Q
    rw [zero_add, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change scalePoint hAB hB (Affine.Point.some x₁ y₁ h₁ + 0) =
        scalePoint hAB hB (Affine.Point.some x₁ y₁ h₁) + 0
      rw [add_zero, add_zero]
    | some x₂ y₂ h₂ =>
      have h₁' := scaled_nonsingular hAB hB h₁
      have h₂' := scaled_nonsingular hAB hB h₂
      by_cases hxy : x₁ = x₂ ∧ y₁ = (Curve A).negY x₂ y₂
      · have hx' := congrArg (fun x => u ^ 2 * x) hxy.1
        have hy' : u ^ 3 * y₁ = (Curve B).negY (u ^ 2 * x₂) (u ^ 3 * y₂) := by
          simpa only [negY_eq, mul_neg] using congrArg (fun y => u ^ 3 * y) hxy.2
        rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        change (0 : (Curve B).Point) =
          Affine.Point.some _ _ h₁' + Affine.Point.some _ _ h₂'
        rw [Affine.Point.add_of_Y_eq hx' hy']
      · have hxy' : ¬(u ^ 2 * x₁ = u ^ 2 * x₂ ∧
            u ^ 3 * y₁ = (Curve B).negY (u ^ 2 * x₂) (u ^ 3 * y₂)) := by
          rintro ⟨hx, hy⟩
          rw [negY_eq, ← mul_neg] at hy
          exact hxy ⟨mul_left_cancel₀ (pow_ne_zero _ hu) hx,
            by simpa only [negY_eq] using mul_left_cancel₀ (pow_ne_zero _ hu) hy⟩
        let ell := (Curve A).slope x₁ x₂ y₁ y₂
        rw [Affine.Point.add_some hxy]
        change Affine.Point.some
            (u ^ 2 * (Curve A).addX x₁ x₂ ell) (u ^ 3 * (Curve A).addY x₁ x₂ y₁ ell)
            (scaled_nonsingular hAB hB (Affine.nonsingular_add h₁ h₂ hxy)) =
          Affine.Point.some _ _ h₁' + Affine.Point.some _ _ h₂'
        rw [Affine.Point.add_some hxy', Affine.Point.some.injEq, slope_scale (A := A) hu]
        exact ⟨(addX_scale (A := A) (B := B) x₁ x₂ ell).symm,
          (addY_scale (A := A) (B := B) x₁ x₂ y₁ ell).symm⟩

/-- The native group map induced by (x,y) ↦ (u²x,u³y). -/
def scale (hu : u ≠ 0) (hAB : u ^ 6 * A = B) (hB : (shortCubic (0 : K) B).Δ ≠ 0) :
    (Curve A).Point →+ (Curve B).Point where
  toFun := scalePoint hAB hB
  map_zero' := rfl
  map_add' := scalePoint_add hu hAB hB

theorem scale_some (hu : u ≠ 0) (hAB : u ^ 6 * A = B)
    (hB : (shortCubic (0 : K) B).Δ ≠ 0) {x y : K} (h : (Curve A).Nonsingular x y) :
    scale hu hAB hB (.some x y h) =
      .some (u ^ 2 * x) (u ^ 3 * y) (scaled_nonsingular hAB hB h) := rfl

private theorem inverse_parameters (hu : u ≠ 0) (hAB : u ^ 6 * A = B) :
    u⁻¹ ^ 6 * B = A := by
  rw [← hAB, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]

private theorem inverse_powers_scale (hu : u ≠ 0) (n : ℕ) (z : K) :
    u⁻¹ ^ n * (u ^ n * z) = z := by
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]

/-- Coordinate scaling is an equivalence, with inverse scaling by u⁻¹. -/
def scaleEquiv (hu : u ≠ 0) (hAB : u ^ 6 * A = B)
    (hA : (shortCubic (0 : K) A).Δ ≠ 0) (hB : (shortCubic (0 : K) B).Δ ≠ 0) :
    (Curve A).Point ≃+ (Curve B).Point where
  toFun := scale hu hAB hB
  invFun := scale (inv_ne_zero hu) (inverse_parameters hu hAB) hA
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      rw [scale_some, scale_some, Affine.Point.some.injEq]
      exact ⟨inverse_powers_scale hu 2 x, inverse_powers_scale hu 3 y⟩
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      rw [scale_some, scale_some, Affine.Point.some.injEq]
      exact ⟨by simpa only [inv_inv] using inverse_powers_scale (inv_ne_zero hu) 2 x,
        by simpa only [inv_inv] using inverse_powers_scale (inv_ne_zero hu) 3 y⟩
  map_add' := map_add (scale hu hAB hB)

theorem scaleEquiv_some (hu : u ≠ 0) (hAB : u ^ 6 * A = B)
    (hA : (shortCubic (0 : K) A).Δ ≠ 0) (hB : (shortCubic (0 : K) B).Δ ≠ 0)
    {x y : K} (h : (Curve A).Nonsingular x y) :
    scaleEquiv hu hAB hA hB (.some x y h) =
      .some (u ^ 2 * x) (u ^ 3 * y) (scaled_nonsingular hAB hB h) := rfl

end
end ManuscriptAudit.CubicPointScaling

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicPointScaling.scale_some,
      ``ManuscriptAudit.CubicPointScaling.scaleEquiv,
      ``ManuscriptAudit.CubicPointScaling.scaleEquiv_some] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
