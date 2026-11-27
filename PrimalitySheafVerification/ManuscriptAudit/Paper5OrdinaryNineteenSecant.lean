import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.CubicTriplingCoordinates
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenAlgebra

/-! Secant coordinates for the characteristic-nineteen geometric Frobenius. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenSecant

open CubicTriplingCoordinates CubicTripleAbscissa Paper5OrdinaryNineteenAlgebra

noncomputable section

variable {K : Type*} [Field K] [CharP K 19]

def doubleX (x : K) : K :=
  x * (rotatedDoubleNumerator (x ^ 3) / doubleDenominator (x ^ 3))

def minusDoubleY (x y : K) : K :=
  -y * (doubleOrdinateNumerator (x ^ 3) / doubleOrdinateDenominator (x ^ 3))

def tripleX (x : K) : K :=
  x * (tripleNumerator (x ^ 3) / tripleDenominator (x ^ 3))

def tripleY (x y : K) : K :=
  y * (tripleOrdinateNumerator (x ^ 3) /
    (thirdSlopeDenominator (x ^ 3) * tripleDenominator (x ^ 3)))

def lastSlope (x y : K) : K :=
  (y / x) * (lastSlopeNumerator (x ^ 3) / ((x ^ 3 + 1) * (x ^ 3 + 4)))

private theorem tripleDen_ne_zero {t : K} (ht : t ≠ 0) (hg : t + 4 ≠ 0) :
    tripleDenominator t ≠ 0 :=
  mul_ne_zero (mul_ne_zero (numeral_ne_zero 9 (by decide)) ht) (pow_ne_zero _ hg)

private theorem doubleDen_ne_zero {t : K} (hs : t + 1 ≠ 0) : doubleDenominator t ≠ 0 :=
  mul_ne_zero (numeral_ne_zero 4 (by decide)) hs

private theorem doubleOrdDen_ne_zero {t : K} (hs : t + 1 ≠ 0) :
    doubleOrdinateDenominator t ≠ 0 :=
  mul_ne_zero (numeral_ne_zero 8 (by decide)) (pow_ne_zero _ hs)

private theorem slopeDen_ne_zero {t : K} (hs : t + 1 ≠ 0) (hg : t + 4 ≠ 0) :
    thirdSlopeDenominator t ≠ 0 :=
  mul_ne_zero (mul_ne_zero (numeral_ne_zero 6 (by decide)) hs) hg

theorem tripleX_correct {x : K} (hx : x ≠ 0) (hg : x ^ 3 + 4 ≠ 0) :
    numerator 1 x = tripleX x * denominator 1 x := by
  rw [triple_numerator_eq]
  symm
  calc
    _ = (tripleNumerator (x ^ 3) / tripleDenominator (x ^ 3)) * (denominator 1 x * x) := by
      unfold tripleX
      ring
    _ = _ := by
      rw [triple_denominator_mul_abscissa, div_mul_cancel₀ _ (tripleDen_ne_zero (pow_ne_zero _ hx) hg)]

private theorem thirdSlope_normalized {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hg : x ^ 3 + 4 ≠ 0) (he : y ^ 2 = x ^ 3 + 1) :
    thirdSlope 1 x y = (y / x) * (thirdSlopeNumerator (x ^ 3) / thirdSlopeDenominator (x ^ 3)) := by
  have h₂ : (2 : K) ≠ 0 := numeral_ne_zero 2 (by decide)
  have h₃ : (3 : K) ≠ 0 := numeral_ne_zero 3 (by decide)
  have h₆ : (6 : K) ≠ 0 := numeral_ne_zero 6 (by decide)
  have hs : x ^ 3 + 1 ≠ 0 := he ▸ pow_ne_zero 2 hy
  calc
    _ = (y / x) * (8 * y ^ 2 / (3 * (x ^ 3 + 4)) - 3 * x ^ 3 / (2 * y ^ 2)) := by
      unfold thirdSlope
      simp only [mul_one]
      field_simp [h₂, h₃, hx, hy, hg] <;> ring
    _ = _ := by
      rw [he, ← third_slope_numerator_eq]
      unfold thirdSlopeDenominator
      field_simp [h₂, h₃, h₆, hx, hg, hs] <;> ring

theorem tripleY_correct {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hg : x ^ 3 + 4 ≠ 0) (he : y ^ 2 = x ^ 3 + 1) :
    thirdSlope 1 x y * (x - tripleX x) - y = tripleY x y := by
  have hs : x ^ 3 + 1 ≠ 0 := he ▸ pow_ne_zero 2 hy
  have hW := slopeDen_ne_zero hs hg
  have hD := tripleDen_ne_zero (pow_ne_zero 3 hx) hg
  rw [thirdSlope_normalized hx hy hg he]
  unfold tripleX tripleY tripleOrdinateNumerator
  field_simp [hx, hW, hD] <;> ring

private theorem fractional_gap (t : K) (ht : t ≠ 0) (hs : t + 1 ≠ 0) (hg : t + 4 ≠ 0) :
    rotatedDoubleNumerator t / doubleDenominator t - tripleNumerator t / tripleDenominator t =
      abscissaGap t / (doubleDenominator t * tripleDenominator t) := by
  unfold abscissaGap
  field_simp [doubleDen_ne_zero hs, tripleDen_ne_zero ht hg] <;> ring

private theorem gap_ne_zero {t : K} (h1 : t ≠ 1) : abscissaGap t ≠ 0 := by
  rw [abscissa_gap]
  exact mul_ne_zero (numeral_ne_zero 9 (by decide)) (sub_ne_zero.mpr h1)

theorem abscissas_distinct {x : K} (hx : x ≠ 0) (hs : x ^ 3 + 1 ≠ 0) (hg : x ^ 3 + 4 ≠ 0)
    (h1 : x ^ 3 ≠ 1) : doubleX x ≠ tripleX x := by
  apply sub_ne_zero.mp
  unfold doubleX tripleX
  rw [← mul_sub, fractional_gap _ (pow_ne_zero _ hx) hs hg]
  exact mul_ne_zero hx (div_ne_zero (gap_ne_zero h1)
    (mul_ne_zero (doubleDen_ne_zero hs) (tripleDen_ne_zero (pow_ne_zero _ hx) hg)))

private theorem fractional_slope (t : K) (ht : t ≠ 0) (hs : t + 1 ≠ 0)
    (hg : t + 4 ≠ 0) (h1 : t ≠ 1) :
    (-doubleOrdinateNumerator t / doubleOrdinateDenominator t -
      tripleOrdinateNumerator t / (thirdSlopeDenominator t * tripleDenominator t)) /
      (rotatedDoubleNumerator t / doubleDenominator t - tripleNumerator t / tripleDenominator t) =
      lastSlopeNumerator t / ((t + 1) * (t + 4)) := by
  have hV := doubleOrdDen_ne_zero hs
  have hU := doubleDen_ne_zero hs
  have hW := slopeDen_ne_zero hs hg
  have hD := tripleDen_ne_zero ht hg
  have hG := gap_ne_zero h1
  have hF := mul_ne_zero hs hg
  have h₆ : (6 : K) ≠ 0 := numeral_ne_zero 6 (by decide)
  rw [fractional_gap t ht hs hg]
  calc
    _ = (doubleDenominator t *
      (-doubleOrdinateNumerator t * thirdSlopeDenominator t * tripleDenominator t -
        tripleOrdinateNumerator t * doubleOrdinateDenominator t)) /
      (doubleOrdinateDenominator t * thirdSlopeDenominator t * abscissaGap t) := by
      field_simp [hV, hU, hW, hD, hG] <;> ring
    _ = _ := by
      rw [last_slope_identity, show thirdSlopeDenominator t = 6 * ((t + 1) * (t + 4)) by
        unfold thirdSlopeDenominator
        ring]
      field_simp [hV, h₆, hG, hs, hg, hF] <;> ring

theorem lastSlope_correct {x y : K} (hx : x ≠ 0) (hs : x ^ 3 + 1 ≠ 0)
    (hg : x ^ 3 + 4 ≠ 0) (h1 : x ^ 3 ≠ 1) :
    (minusDoubleY x y - tripleY x y) / (doubleX x - tripleX x) = lastSlope x y := by
  let t := x ^ 3
  have hY : minusDoubleY x y - tripleY x y =
      y * (-doubleOrdinateNumerator t / doubleOrdinateDenominator t -
        tripleOrdinateNumerator t / (thirdSlopeDenominator t * tripleDenominator t)) := by
    unfold minusDoubleY tripleY
    simp only [t, neg_div]
    ring
  have hX : doubleX x - tripleX x =
      x * (rotatedDoubleNumerator t / doubleDenominator t - tripleNumerator t / tripleDenominator t) := by
    unfold doubleX tripleX
    simp only [t]
    ring
  rw [hY, hX]
  calc
    _ = (y / x) * ((-doubleOrdinateNumerator t / doubleOrdinateDenominator t -
        tripleOrdinateNumerator t / (thirdSlopeDenominator t * tripleDenominator t)) /
        (rotatedDoubleNumerator t / doubleDenominator t - tripleNumerator t / tripleDenominator t)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [fractional_slope t (pow_ne_zero _ hx) hs hg h1] <;> rfl

private theorem fractional_abscissa (t : K) (ht : t ≠ 0) (hs : t + 1 ≠ 0) (hg : t + 4 ≠ 0) :
    9 * lastSlopeNumerator t ^ 2 / ((t + 1) * tripleDenominator t) -
      rotatedDoubleNumerator t / doubleDenominator t - tripleNumerator t / tripleDenominator t = t ^ 6 := by
  have hD := tripleDen_ne_zero ht hg
  have hU := doubleDen_ne_zero hs
  have h₄ : (4 : K) ≠ 0 := numeral_ne_zero 4 (by decide)
  apply mul_right_cancel₀ (mul_ne_zero hU hD)
  calc
    (9 * lastSlopeNumerator t ^ 2 / ((t + 1) * tripleDenominator t) -
        rotatedDoubleNumerator t / doubleDenominator t - tripleNumerator t / tripleDenominator t) *
        (doubleDenominator t * tripleDenominator t) =
      36 * lastSlopeNumerator t ^ 2 - rotatedDoubleNumerator t * tripleDenominator t -
        4 * (t + 1) * tripleNumerator t := by
      unfold doubleDenominator
      field_simp [hD, hs, h₄] <;> ring
    _ = 4 * (t + 1) * tripleDenominator t * t ^ 6 := last_abscissa_identity t
    _ = t ^ 6 * (doubleDenominator t * tripleDenominator t) := by unfold doubleDenominator; ring

theorem last_abscissa {x y : K} (hx : x ≠ 0) (hg : x ^ 3 + 4 ≠ 0)
    (he : y ^ 2 = x ^ 3 + 1) (hs : x ^ 3 + 1 ≠ 0) :
    lastSlope x y ^ 2 - doubleX x - tripleX x = x ^ 19 := by
  let t := x ^ 3
  have h₉ : (9 : K) ≠ 0 := numeral_ne_zero 9 (by decide)
  have hM : lastSlope x y ^ 2 = x * (9 * lastSlopeNumerator t ^ 2 / ((t + 1) * tripleDenominator t)) := by
    unfold lastSlope tripleDenominator
    rw [mul_pow, div_pow, div_pow, he]
    dsimp only [t]
    field_simp [hx, hg, hs, h₉] <;> ring
  calc
    lastSlope x y ^ 2 - doubleX x - tripleX x =
      x * (9 * lastSlopeNumerator t ^ 2 / ((t + 1) * tripleDenominator t) -
        rotatedDoubleNumerator t / doubleDenominator t - tripleNumerator t / tripleDenominator t) := by
      rw [hM]
      unfold doubleX tripleX
      dsimp only [t]
      ring
    _ = x ^ 19 := by rw [fractional_abscissa t (pow_ne_zero _ hx) hs hg]; dsimp only [t]; ring

private theorem fractional_ordinate (t : K) (hs : t + 1 ≠ 0) (hg : t + 4 ≠ 0) :
    lastSlopeNumerator t / ((t + 1) * (t + 4)) *
      (rotatedDoubleNumerator t / doubleDenominator t - t ^ 6) +
      doubleOrdinateNumerator t / doubleOrdinateDenominator t = (t + 1) ^ 9 := by
  have h₄ : (4 : K) ≠ 0 := numeral_ne_zero 4 (by decide)
  have h₈ : (8 : K) ≠ 0 := numeral_ne_zero 8 (by decide)
  apply mul_right_cancel₀ (mul_ne_zero hg (doubleOrdDen_ne_zero hs))
  calc
    (lastSlopeNumerator t / ((t + 1) * (t + 4)) *
        (rotatedDoubleNumerator t / doubleDenominator t - t ^ 6) +
        doubleOrdinateNumerator t / doubleOrdinateDenominator t) *
        ((t + 4) * doubleOrdinateDenominator t) =
      2 * lastSlopeNumerator t * (rotatedDoubleNumerator t - doubleDenominator t * t ^ 6) +
        doubleOrdinateNumerator t * (t + 4) := by
      unfold doubleDenominator doubleOrdinateDenominator
      field_simp [hs, hg, h₄, h₈] <;> ring
    _ = (t + 1) ^ 9 * (t + 4) * doubleOrdinateDenominator t := last_ordinate_identity t
    _ = (t + 1) ^ 9 * ((t + 4) * doubleOrdinateDenominator t) := by ring

theorem last_ordinate {x y : K} (hx : x ≠ 0) (hg : x ^ 3 + 4 ≠ 0)
    (he : y ^ 2 = x ^ 3 + 1) (hs : x ^ 3 + 1 ≠ 0) :
    lastSlope x y * (doubleX x - x ^ 19) - minusDoubleY x y = y ^ 19 := by
  let t := x ^ 3
  have hpow : x ^ 19 = x * t ^ 6 := by dsimp only [t]; ring
  calc
    lastSlope x y * (doubleX x - x ^ 19) - minusDoubleY x y =
      y * (lastSlopeNumerator t / ((t + 1) * (t + 4)) *
        (rotatedDoubleNumerator t / doubleDenominator t - t ^ 6) +
        doubleOrdinateNumerator t / doubleOrdinateDenominator t) := by
      rw [hpow]
      unfold lastSlope doubleX minusDoubleY
      dsimp only [t]
      field_simp [hx] <;> ring
    _ = y ^ 19 := by rw [fractional_ordinate t hs hg]; dsimp only [t]; rw [← he]; ring

end
end ManuscriptAudit.Paper5OrdinaryNineteenSecant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenSecant.tripleX_correct,
      ``ManuscriptAudit.Paper5OrdinaryNineteenSecant.tripleY_correct,
      ``ManuscriptAudit.Paper5OrdinaryNineteenSecant.abscissas_distinct,
      ``ManuscriptAudit.Paper5OrdinaryNineteenSecant.lastSlope_correct,
      ``ManuscriptAudit.Paper5OrdinaryNineteenSecant.last_abscissa,
      ``ManuscriptAudit.Paper5OrdinaryNineteenSecant.last_ordinate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
