import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard

/-! Native abscissa and ordinate formulas for the two parts of the flex group. -/

namespace ManuscriptAudit.CubicThreeTorsionOrdinate

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsion

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] {A : K}

abbrev Curve (A : K) := CubicAffine (0 : K) A

def abscissa : (Curve A).Point → K
  | .zero => 0
  | .some x _ _ => x

def ordinate : (Curve A).Point → K
  | .zero => 0
  | .some _ y _ => y

@[simp] theorem abscissa_zero : abscissa (0 : (Curve A).Point) = 0 := rfl

@[simp] theorem ordinate_zero : ordinate (0 : (Curve A).Point) = 0 := rfl

@[simp] theorem abscissa_some {x y : K} (h : (Curve A).Nonsingular x y) :
    abscissa (Affine.Point.some x y h) = x := rfl

@[simp] theorem ordinate_some {x y : K} (h : (Curve A).Nonsingular x y) :
    ordinate (Affine.Point.some x y h) = y := rfl

private theorem negY_eq (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

@[simp] theorem abscissa_neg (P : (Curve A).Point) : abscissa (-P) = abscissa P := by
  cases P with
  | zero => rfl
  | some x y h => simp only [Affine.Point.neg_some, abscissa_some]

@[simp] theorem ordinate_neg (P : (Curve A).Point) : ordinate (-P) = -ordinate P := by
  cases P with
  | zero =>
    change (0 : K) = -0
    exact neg_zero.symm
  | some x y h => simp only [Affine.Point.neg_some, ordinate_some, negY_eq]

theorem nonsingular_iff (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) (x y : K) :
    (Curve A).Nonsingular x y ↔ y ^ 2 = x ^ 3 + A := by
  rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, Affine.equation_iff]
  simp [Curve, CubicAffine, shortCubic]

theorem ordinate_eq_of_two_squares {a b : K} (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b := by
  have hz : (a - b) * (a + b) = 0 := by
    calc
      _ = a ^ 2 - b ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hz with hsub | hadd
  · exact Or.inl (sub_eq_zero.mp hsub)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hadd)

theorem ordinate_nonzero_of_horizontal {b : K} (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hb : b ^ 2 = -(3 * A)) : b ≠ 0 := by
  intro h
  exact neg_ne_zero.mpr (mul_ne_zero h₃ hA) (by simpa [h] using hb.symm)

/-- Adding a vertical flex preserves the ordinate of a nonvertical flex. -/
theorem ordinate_add_vertical {x a b : K} (hx : x ≠ 0)
    (hcube : x ^ 3 = -(4 * A)) (ha : a ^ 2 = A) (hb : b ^ 2 = -(3 * A))
    (hU : (Curve A).Nonsingular x b) (hT : (Curve A).Nonsingular 0 a) :
    ordinate ((Affine.Point.some x b hU : (Curve A).Point) + Affine.Point.some 0 a hT) = b := by
  let W := Curve A
  let ell := W.slope x 0 b a
  have hslope : ell = (b - a) / x := by
    change W.slope x 0 b a = _
    rw [Affine.slope_of_X_ne hx, sub_zero]
  have hmul : ell * x = b - a := by rw [hslope, div_mul_cancel₀ _ hx]
  have hcubeDiff : (b - a) ^ 3 = 8 * A * a := by
    calc
      _ = b * b ^ 2 - 3 * b ^ 2 * a + 3 * b * a ^ 2 - a * a ^ 2 := by ring
      _ = _ := by rw [ha, hb]; ring
  have hell : ell ^ 3 = -(2 * a) := by
    apply mul_right_cancel₀ (pow_ne_zero 3 hx)
    calc
      ell ^ 3 * x ^ 3 = (ell * x) ^ 3 := (mul_pow _ _ _).symm
      _ = (b - a) ^ 3 := congrArg (fun t : K => t ^ 3) hmul
      _ = 8 * A * a := hcubeDiff
      _ = -(2 * a) * x ^ 3 := by rw [hcube]; ring
  rw [Affine.Point.add_of_X_ne hx, ordinate_some]
  change W.addY x 0 b ell = b
  calc
    _ = -(ell * (ell ^ 2 - x - x) + b) := by
      simp [W, Curve, CubicAffine, shortCubic, Affine.addY, Affine.negAddY, Affine.addX,
        Affine.negY]
    _ = -ell ^ 3 + 2 * (ell * x) - b := by ring
    _ = b := by rw [hell, hmul]; ring

theorem ordinate_sub_vertical {x a b : K} (hx : x ≠ 0)
    (hcube : x ^ 3 = -(4 * A)) (ha : a ^ 2 = A) (hb : b ^ 2 = -(3 * A))
    (hU : (Curve A).Nonsingular x b) (hT : (Curve A).Nonsingular 0 a) :
    ordinate ((Affine.Point.some x b hU : (Curve A).Point) - Affine.Point.some 0 a hT) = b := by
  rw [sub_eq_add_neg, Affine.Point.neg_some]
  exact ordinate_add_vertical hx hcube (by rw [negY_eq, neg_sq, ha]) hb hU _

end
end ManuscriptAudit.CubicThreeTorsionOrdinate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeTorsionOrdinate.abscissa_neg,
      ``ManuscriptAudit.CubicThreeTorsionOrdinate.ordinate_neg,
      ``ManuscriptAudit.CubicThreeTorsionOrdinate.ordinate_eq_of_two_squares,
      ``ManuscriptAudit.CubicThreeTorsionOrdinate.ordinate_add_vertical,
      ``ManuscriptAudit.CubicThreeTorsionOrdinate.ordinate_sub_vertical] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
