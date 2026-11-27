import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.CubicTriplingSurjective

/-! The native tripling formula with its ordinate specified by the actual secant. -/

namespace ManuscriptAudit.CubicTriplingCoordinates

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicTripleAbscissa CubicTriplingSurjective

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A : K}

theorem negY_eq (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

theorem addX_eq (x u ell : K) : (Curve A).addX x u ell = ell ^ 2 - x - u := by
  simp [Curve, CubicAffine, shortCubic, Affine.addX]

theorem addY_eq (x u y ell : K) :
    (Curve A).addY x u y ell = ell * (x - (Curve A).addX x u ell) - y := by
  rw [Affine.addY, negY_eq]
  simp only [Affine.negAddY]
  ring

def thirdSlope (A x y : K) : K := 8 * y ^ 3 / (3 * x * (x ^ 3 + 4 * A)) - 3 * x ^ 2 / (2 * y)

set_option maxHeartbeats 600000 in
/-- The computed abscissa and secant give the actual native tripled point. -/
theorem triple_some_coordinates {x y u : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) (hy : y ≠ 0)
    (hx : x ≠ 0) (hg : x ^ 3 + 4 * A ≠ 0)
    (hU : numerator A x = u * denominator A x)
    (hP : (Curve A).Nonsingular x y) :
    ∃ h : (Curve A).Nonsingular u (thirdSlope A x y * (x - u) - y),
      (3 : ℕ) • (Affine.Point.some x y hP : (Curve A).Point) =
        Affine.Point.some u (thirdSlope A x y * (x - u) - y) h := by
  let W := Curve A
  let g := x ^ 3 + 4 * A
  have h₄ : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero _ h₂
  have hEq := (nonsingular_iff hΔ x y).mp hP
  have hD : denominator A x ≠ 0 := by
    have hF : denominator A x = (3 * x * g) ^ 2 := by
      dsimp only [g, denominator]
      ring
    rw [hF]
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero h₃ hx) hg)
  have hyN : y ≠ W.negY x y := by
    change y ≠ (Curve A).negY x y
    rw [negY_eq]
    intro he
    exact (mul_ne_zero h₂ hy) (by linear_combination he)
  let ell := W.slope x x y y
  have hEll : ell = 3 * x ^ 2 / (2 * y) := by
    change W.slope x x y y = _
    rw [Affine.slope_of_Y_ne rfl hyN, negY_eq, sub_neg_eq_add, ← two_mul]
    simp [W, Curve, CubicAffine, shortCubic]
  let x₂ := W.addX x x ell
  let y₂ := W.addY x x y ell
  have hX₂ : x₂ = ell ^ 2 - x - x := addX_eq x x ell
  have hY₂ : y₂ = ell * (x - x₂) - y := addY_eq x x y ell
  have hDiff : x₂ - x = -(3 * x * g) / (4 * y ^ 2) := by
    rw [hX₂, hEll]
    calc
      _ = (9 * x ^ 4 - 12 * x * y ^ 2) / (4 * y ^ 2) := by
        field_simp [h₂, h₄, hy] <;> ring
      _ = _ := by
        apply congrArg (fun a : K => a / (4 * y ^ 2))
        rw [hEq]
        dsimp only [g]
        ring
  have hDiff₀ : x₂ - x ≠ 0 := by
    rw [hDiff]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h₃ hx) hg))
      (mul_ne_zero h₄ (pow_ne_zero _ hy))
  have hx₂ : x ≠ x₂ := (sub_ne_zero.mp hDiff₀).symm
  let m := W.slope x x₂ y y₂
  have hM : m = thirdSlope A x y := by
    change W.slope x x₂ y y₂ = _
    rw [Affine.slope_of_X_ne hx₂, hY₂]
    calc
      _ = -(2 * y) / (x₂ - x) - ell := by
        field_simp [sub_ne_zero.mpr hx₂, hDiff₀] <;> ring
      _ = _ := by
        rw [hDiff, hEll]
        unfold thirdSlope
        field_simp [h₄, h₂, h₃, hy, hx, hg, show g ≠ 0 from hg] <;> ring
  have h₂P : W.Nonsingular x₂ y₂ :=
    Affine.nonsingular_add hP hP (fun h => hyN h.2)
  have h₃P : W.Nonsingular (W.addX x x₂ m) (W.addY x x₂ y m) :=
    Affine.nonsingular_add hP h₂P (fun h => hx₂ h.1)
  have hTriple : (3 : ℕ) • (Affine.Point.some x y hP : W.Point) =
      Affine.Point.some (W.addX x x₂ m) (W.addY x x₂ y m) h₃P := by
    rw [show (3 : ℕ) = 1 + 2 by decide, add_nsmul, one_nsmul, two_nsmul,
      Affine.Point.add_of_Y_ne hyN]
    exact Affine.Point.add_of_X_ne hx₂
  obtain ⟨v, hv, he⟩ := triple_some h₂ h₃ hΔ hD hU hP
  have hxy : W.addX x x₂ m = u ∧ W.addY x x₂ y m = v := by
    simpa only [Affine.Point.some.injEq] using hTriple.symm.trans he
  have hvEq : v = thirdSlope A x y * (x - u) - y := by
    rw [← hxy.2, addY_eq, hxy.1, hM]
  have hv' : (Curve A).Nonsingular u (thirdSlope A x y * (x - u) - y) := by
    simpa only [← hvEq] using hv
  refine ⟨hv', he.trans ?_⟩
  rw [Affine.Point.some.injEq]
  exact ⟨rfl, hvEq⟩

end
end ManuscriptAudit.CubicTriplingCoordinates

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicTriplingCoordinates.triple_some_coordinates
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
