import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCharacteristicFiveDouble

/-! The secant with the fourth multiple gives the fifth multiple away from explicit exceptional points. -/

namespace ManuscriptAudit.CubicCharacteristicFiveSecant

open WeierstrassCurve CubicThreeTorsionOrdinate CubicCharacteristicFiveIdentities
open CubicCharacteristicFiveDouble

noncomputable section

variable {K : Type*} [Field K] [CharP K 5] [DecidableEq K] {A : K}

set_option maxHeartbeats 700000 in
theorem secant_coordinates {x y t : K}
    (hA : A ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (ht : t ≠ 1)
    (hD : t + 1 ≠ 0) (hV : ordinateFactor t ≠ 0)
    (hCube : x ^ 3 = A * t) (hySq : y ^ 2 = A * (t + 1)) :
    let u := x * fourthAbscissaNumerator t / ((t + 1) * ordinateFactor t ^ 2)
    let v := y * fourthOrdinateNumerator t / ((t + 1) ^ 2 * ordinateFactor t ^ 3)
    let l := (y - v) / (x - u)
    x ≠ u ∧ l ^ 2 - x - u = x * t ^ 8 ∧
      l * (x - x * t ^ 8) - y = -(y * (t + 1) ^ 12) := by
  let D := t + 1
  let V := ordinateFactor t
  let M := fourthAbscissaNumerator t
  let N := fourthOrdinateNumerator t
  let T := secantFactor t
  let u := x * M / (D * V ^ 2)
  let v := y * N / (D ^ 2 * V ^ 3)
  let l := (y - v) / (x - u)
  let L := x ^ 2 * T / (2 * y * V)
  change x ≠ u ∧ l ^ 2 - x - u = x * t ^ 8 ∧ l * (x - x * t ^ 8) - y = -(y * D ^ 12)
  have h₂ : (2 : K) ≠ 0 := two_ne
  have h₄ : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero _ h₂
  have huDiff : u - x = x * (2 * (t - 1)) / (D * V ^ 2) := by
    calc
      _ = x * (M - D * V ^ 2) / (D * V ^ 2) := by
        dsimp only [u]
        field_simp [hD, hV] <;> ring
      _ = _ := by rw [show M - D * V ^ 2 = _ from fourth_abscissa_difference t]
  have hvDiff : v - y = y * (t * (t - 1) * T) / (D ^ 2 * V ^ 3) := by
    calc
      _ = y * (N - D ^ 2 * V ^ 3) / (D ^ 2 * V ^ 3) := by
        dsimp only [v]
        field_simp [hD, hV] <;> ring
      _ = _ := by rw [show N - D ^ 2 * V ^ 3 = _ from fourth_ordinate_difference t]
  have hdif : u - x ≠ 0 := by
    rw [huDiff]
    exact div_ne_zero (mul_ne_zero hx (mul_ne_zero h₂ (sub_ne_zero.mpr ht)))
      (mul_ne_zero hD (pow_ne_zero _ hV))
  have hxu : x ≠ u := (sub_ne_zero.mp hdif).symm
  have hL : l = L := by
    change (y - v) / (x - u) = L
    apply (div_eq_iff (sub_ne_zero.mpr hxu)).mpr
    suffices hvu : v - y = L * (u - x) by linear_combination -hvu
    rw [hvDiff, huDiff]
    dsimp only [L]
    have hCubeD : x ^ 3 * D = y ^ 2 * t := by rw [hCube, hySq]; ring
    calc
      _ = (y ^ 2 * t) * ((t - 1) * T) / (y * D ^ 2 * V ^ 3) := by
        field_simp [hy, hD, hV] <;> ring
      _ = (x ^ 3 * D) * ((t - 1) * T) / (y * D ^ 2 * V ^ 3) := by rw [hCubeD]
      _ = _ := by field_simp [h₂, hy, hD, hV] <;> ring
  have hLsq : L ^ 2 = x * (t * T ^ 2) / (4 * D * V ^ 2) := by
    calc
      _ = x * x ^ 3 * T ^ 2 / (4 * y ^ 2 * V ^ 2) := by
        dsimp only [L]
        field_simp [h₂, h₄, hy, hV] <;> ring
      _ = _ := by rw [hCube, hySq]; field_simp [h₄, hA, hD, hV] <;> ring
  refine ⟨hxu, ?_, ?_⟩
  · rw [hL, hLsq]
    calc
      _ = x * (t * T ^ 2 - 4 * (M + D * V ^ 2)) / (4 * D * V ^ 2) := by
        dsimp only [u]
        field_simp [h₄, hD, hV] <;> ring
      _ = _ := by
        rw [show t * T ^ 2 - 4 * (M + D * V ^ 2) = _ from fifth_abscissa t]
        field_simp [h₄, hD, hV] <;> ring
  · rw [hL]
    have hLmul : L * (x - x * t ^ 8) = y * (t * T * (1 - t ^ 8)) / (2 * D * V) := by
      calc
        _ = x ^ 3 * (T * (1 - t ^ 8)) / (2 * y * V) := by
          dsimp only [L]
          field_simp [h₂, hy, hV] <;> ring
        _ = (A * t) * (T * (1 - t ^ 8)) / (2 * y * V) := by rw [hCube]
        _ = (y ^ 2 / D * t) * (T * (1 - t ^ 8)) / (2 * y * V) := by
          rw [hySq]
          field_simp [h₂, hy, hD, hV] <;> ring
        _ = _ := by field_simp [h₂, hy, hD, hV] <;> ring
    rw [hLmul, show t * T * (1 - t ^ 8) = _ from fifth_ordinate t]
    field_simp [h₂, hD, hV] <;> ring

/-- Native multiplication by five in the nondegenerate affine case. -/
theorem five_some_of_secant {x y t : K}
    (hA : A ≠ 0) (hA4 : A ^ 4 = 1) (hx : x ≠ 0) (hy : y ≠ 0) (ht : t ≠ 1)
    (hD : t + 1 ≠ 0) (hV : ordinateFactor t ≠ 0)
    (hCube : x ^ 3 = A * t) (hySq : y ^ 2 = A * (t + 1))
    (hP : (Curve A).Nonsingular x y) :
    ∃ h : (Curve A).Nonsingular (x ^ 25) (-(y ^ 25)),
      (5 : ℕ) • (Affine.Point.some x y hP : (Curve A).Point) =
        Affine.Point.some (x ^ 25) (-(y ^ 25)) h := by
  let W := Curve A
  let P : W.Point := .some x y hP
  let u := -x * (t + 2) / (t + 1)
  let v := y * ordinateFactor t / (t + 1) ^ 2
  let U := x * fourthAbscissaNumerator t / ((t + 1) * ordinateFactor t ^ 2)
  let V := y * fourthOrdinateNumerator t / ((t + 1) ^ 2 * ordinateFactor t ^ 3)
  have hVne : v ≠ 0 := div_ne_zero (mul_ne_zero hy hV) (pow_ne_zero _ hD)
  obtain ⟨h₂Raw, h₂eq⟩ := double_some hA hy hP
  obtain ⟨hu, hv⟩ := normalized_second_coordinates hA hy hD hCube hySq
  change _ = u at hu
  change _ = v at hv
  have h₂P : W.Nonsingular u v := by rw [← hu, ← hv]; exact h₂Raw
  have h₂ : (2 : ℕ) • P = Affine.Point.some u v h₂P := h₂eq.trans (by
    rw [Affine.Point.some.injEq]
    exact ⟨hu, hv⟩)
  obtain ⟨h₄Raw, h₄eq⟩ := double_some hA hVne h₂P
  obtain ⟨hU, hV'⟩ := normalized_fourth_coordinates hA hy hD hV hCube hySq
  change -u * (u ^ 3 + 2 * A) / v ^ 2 = U at hU
  change (2 * u ^ 6 - A ^ 2) / v ^ 3 = V at hV'
  have h₄P : W.Nonsingular U V := by rw [← hU, ← hV']; exact h₄Raw
  have h₄ : (2 : ℕ) • Affine.Point.some u v h₂P = Affine.Point.some U V h₄P := h₄eq.trans (by
    rw [Affine.Point.some.injEq]
    exact ⟨hU, hV'⟩)
  obtain ⟨hxu, hℓx, hℓy⟩ := secant_coordinates hA hx hy ht hD hV hCube hySq
  let l := W.slope x U y V
  have hl : l = (y - V) / (x - U) := Affine.slope_of_X_ne hxu
  have hA8 : A ^ 8 = 1 := by rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, hA4, one_pow]
  have hA12 : A ^ 12 = 1 := by rw [show (12 : ℕ) = 4 * 3 by decide, pow_mul, hA4, one_pow]
  have hx25 : x ^ 25 = x * t ^ 8 := by
    calc
      _ = x * (x ^ 3) ^ 8 := by ring
      _ = _ := by rw [hCube, mul_pow, hA8, one_mul]
  have hy25 : y ^ 25 = y * (t + 1) ^ 12 := by
    calc
      _ = y * (y ^ 2) ^ 12 := by ring
      _ = _ := by rw [hySq, mul_pow, hA12, one_mul]
  have hX : W.addX x U l = x ^ 25 := by
    change (Curve A).addX x U l = _
    rw [CubicCharacteristicFiveDouble.addX, hl, hx25]
    exact hℓx
  have hY : W.addY x U y l = -(y ^ 25) := by
    change (Curve A).addY x U y l = _
    rw [CubicCharacteristicFiveDouble.addY, show (Curve A).addX x U l = _ from hX, hl, hx25, hy25]
    exact hℓy
  have hs := Affine.nonsingular_add hP h₄P (fun h => hxu h.1)
  have hs' : W.Nonsingular (x ^ 25) (-(y ^ 25)) := by rw [← hX, ← hY]; exact hs
  refine ⟨hs', ?_⟩
  change (5 : ℕ) • P = _
  rw [show (5 : ℕ) = 1 + 2 * 2 by decide, add_nsmul, one_nsmul, mul_nsmul]
  change P + 2 • (2 • P) = _
  rw [h₂, h₄]
  change Affine.Point.some x y hP + Affine.Point.some U V h₄P = _
  rw [Affine.Point.add_of_X_ne hxu, Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

end
end ManuscriptAudit.CubicCharacteristicFiveSecant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCharacteristicFiveSecant.secant_coordinates,
      ``ManuscriptAudit.CubicCharacteristicFiveSecant.five_some_of_secant] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
