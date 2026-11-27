import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.CubicCharacteristicFiveIdentities
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! The actual affine doubling and fourth-multiple formulas in characteristic five. -/

namespace ManuscriptAudit.CubicCharacteristicFiveDouble

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicCharacteristicFiveIdentities

noncomputable section

variable {K : Type*} [Field K] [CharP K 5] [DecidableEq K] {A : K}

theorem two_ne : (2 : K) ≠ 0 := by
  simpa only [Nat.cast_ofNat, CharP.cast_eq_zero_iff K 5] using
    (show ¬ 5 ∣ (2 : ℕ) by decide)

theorem three_ne : (3 : K) ≠ 0 := by
  simpa only [Nat.cast_ofNat, CharP.cast_eq_zero_iff K 5] using
    (show ¬ 5 ∣ (3 : ℕ) by decide)

theorem negY (x y : K) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

theorem addX (x u l : K) : (Curve A).addX x u l = l ^ 2 - x - u := by
  simp [Curve, CubicAffine, shortCubic, Affine.addX]

theorem addY (x u y l : K) :
    (Curve A).addY x u y l = l * (x - (Curve A).addX x u l) - y := by
  rw [Affine.addY, negY]
  simp only [Affine.negAddY]
  ring

/-- The doubled point in unnormalized coordinates. -/
theorem double_some {x y : K} (hA : A ≠ 0) (hy : y ≠ 0)
    (hP : (Curve A).Nonsingular x y) :
    ∃ h : (Curve A).Nonsingular (-x * (x ^ 3 + 2 * A) / y ^ 2) ((2 * x ^ 6 - A ^ 2) / y ^ 3),
      (2 : ℕ) • (Affine.Point.some x y hP : (Curve A).Point) =
        Affine.Point.some (-x * (x ^ 3 + 2 * A) / y ^ 2) ((2 * x ^ 6 - A ^ 2) / y ^ 3) h := by
  let W := Curve A
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hEq := (nonsingular_iff (CubicThreeTorsionCard.shortCubic_discriminant_ne_zero two_ne three_ne hA)
    x y).mp hP
  have hyNeg : y ≠ W.negY x y := by
    change y ≠ (Curve A).negY x y
    rw [negY]
    intro h
    apply mul_ne_zero two_ne hy
    calc
      _ = y + y := two_mul y
      _ = -y + y := congrArg (fun v => v + y) h
      _ = 0 := neg_add_cancel y
  let l := W.slope x x y y
  have h3neg : (3 : K) = -2 := by linear_combination h5
  have hl : l = -x ^ 2 / y := by
    change (Curve A).slope x x y y = _
    rw [Affine.slope_of_Y_ne rfl hyNeg, negY, sub_neg_eq_add, ← two_mul]
    simp only [Curve, CubicAffine, shortCubic, mul_zero, zero_mul, add_zero, sub_zero]
    rw [h3neg]
    field_simp [two_ne (K := K), hy]
    <;> ring
  have hX : W.addX x x l = -x * (x ^ 3 + 2 * A) / y ^ 2 := by
    change (Curve A).addX x x l = _
    rw [addX, hl]
    apply (eq_div_iff (pow_ne_zero 2 hy)).mpr
    calc
      _ = x ^ 4 - 2 * x * y ^ 2 := by field_simp [hy] <;> ring
      _ = _ := by rw [hEq]; ring
  have hY : W.addY x x y l = (2 * x ^ 6 - A ^ 2) / y ^ 3 := by
    change (Curve A).addY x x y l = _
    rw [addY, show (Curve A).addX x x l = _ from hX, hl]
    apply (eq_div_iff (pow_ne_zero 3 hy)).mpr
    have hy4 : y ^ 4 = (x ^ 3 + A) ^ 2 := by
      rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hEq]
    calc
      _ = -x ^ 3 * y ^ 2 - x ^ 3 * (x ^ 3 + 2 * A) - y ^ 4 := by
        field_simp [hy] <;> ring
      _ = _ := by rw [hEq, hy4]; linear_combination (-x ^ 6 - A * x ^ 3) * h5
  have h := Affine.nonsingular_add hP hP (fun h => hyNeg h.2)
  have h' : W.Nonsingular (-x * (x ^ 3 + 2 * A) / y ^ 2) ((2 * x ^ 6 - A ^ 2) / y ^ 3) := by
    rw [← hX, ← hY]
    exact h
  refine ⟨h', ?_⟩
  rw [two_nsmul, Affine.Point.add_of_Y_ne hyNeg, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

variable {x y t : K}

theorem normalized_second_coordinates (hA : A ≠ 0) (hy : y ≠ 0)
    (hD : t + 1 ≠ 0) (hx : x ^ 3 = A * t) (hySq : y ^ 2 = A * (t + 1)) :
    -x * (x ^ 3 + 2 * A) / y ^ 2 = -x * (t + 2) / (t + 1) ∧
      (2 * x ^ 6 - A ^ 2) / y ^ 3 = y * ordinateFactor t / (t + 1) ^ 2 := by
  constructor
  · rw [hx, hySq]
    field_simp [hA, hD] <;> ring
  · calc
      _ = A ^ 2 * ordinateFactor t / y ^ 3 := by
        congr 1
        rw [show x ^ 6 = (x ^ 3) ^ 2 by ring, hx]
        unfold ordinateFactor
        ring
      _ = (y ^ 2) ^ 2 * ordinateFactor t / (y ^ 3 * (t + 1) ^ 2) := by
        rw [hySq]
        field_simp [hy, hD] <;> ring
      _ = _ := by field_simp [hy, hD] <;> ring

theorem normalized_fourth_coordinates (hA : A ≠ 0) (hy : y ≠ 0)
    (hD : t + 1 ≠ 0) (hV : ordinateFactor t ≠ 0)
    (hx : x ^ 3 = A * t) (hySq : y ^ 2 = A * (t + 1)) :
    let u := -x * (t + 2) / (t + 1)
    let v := y * ordinateFactor t / (t + 1) ^ 2
    -u * (u ^ 3 + 2 * A) / v ^ 2 =
        x * fourthAbscissaNumerator t / ((t + 1) * ordinateFactor t ^ 2) ∧
      (2 * u ^ 6 - A ^ 2) / v ^ 3 =
        y * fourthOrdinateNumerator t / ((t + 1) ^ 2 * ordinateFactor t ^ 3) := by
  dsimp only
  have hu3 : (-x * (t + 2) / (t + 1)) ^ 3 = -A * t * (t + 2) ^ 3 / (t + 1) ^ 3 := by
    calc
      _ = -(x ^ 3) * (t + 2) ^ 3 / (t + 1) ^ 3 := by field_simp [hD] <;> ring
      _ = _ := by rw [hx]; ring
  constructor
  · rw [hu3]
    calc
      _ = x * fourthAbscissaNumerator t * A / (y ^ 2 * ordinateFactor t ^ 2) := by
        unfold fourthAbscissaNumerator
        field_simp [hy, hD, hV] <;> ring
      _ = _ := by rw [hySq]; field_simp [hA, hD, hV] <;> ring
  · rw [show (-x * (t + 2) / (t + 1)) ^ 6 = ((-x * (t + 2) / (t + 1)) ^ 3) ^ 2 by ring, hu3]
    calc
      _ = A ^ 2 * fourthOrdinateNumerator t / (y ^ 3 * ordinateFactor t ^ 3) := by
        unfold fourthOrdinateNumerator
        field_simp [hy, hD, hV] <;> ring
      _ = (y ^ 2) ^ 2 * fourthOrdinateNumerator t /
          (y ^ 3 * (t + 1) ^ 2 * ordinateFactor t ^ 3) := by
        rw [hySq]
        field_simp [hy, hD, hV] <;> ring
      _ = _ := by field_simp [hy, hD, hV] <;> ring

end
end ManuscriptAudit.CubicCharacteristicFiveDouble

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCharacteristicFiveDouble.double_some,
      ``ManuscriptAudit.CubicCharacteristicFiveDouble.normalized_second_coordinates,
      ``ManuscriptAudit.CubicCharacteristicFiveDouble.normalized_fourth_coordinates] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
