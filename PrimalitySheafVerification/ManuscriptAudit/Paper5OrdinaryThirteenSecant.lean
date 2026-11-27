import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.CubicTriplingCoordinates
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenAlgebra

/-! Rational secant formulas for the characteristic-thirteen centered cubic. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenSecant

open CubicTriplingCoordinates CubicTripleAbscissa Paper5OrdinaryThirteenAlgebra

noncomputable section

variable {K : Type*} [Field K] [CharP K 13]

def tripleX (x : K) : K := x * (tripleNum (x ^ 3) / tripleDen (x ^ 3))

def tripleY (x y : K) : K := thirdSlope 1 x y * (x - tripleX x) - y

def lastSlope (x y : K) : K := (y / x) * (secantNum (x ^ 3) / (x ^ 3 + 4))

private theorem tripleDen_ne_zero {x : K} (hx : x ≠ 0) (hg : x ^ 3 + 4 ≠ 0) :
    tripleDen (x ^ 3) ≠ 0 := by
  unfold tripleDen
  exact mul_ne_zero (mul_ne_zero (numeral_ne_zero 9 (by decide)) (pow_ne_zero _ hx))
    (pow_ne_zero _ hg)

theorem tripleX_correct {x : K} (hx : x ≠ 0) (hg : x ^ 3 + 4 ≠ 0) :
    numerator 1 x = tripleX x * denominator 1 x := by
  rw [numerator_eq]
  symm
  calc
    _ = (tripleNum (x ^ 3) / tripleDen (x ^ 3)) * (denominator 1 x * x) := by
      unfold tripleX
      ring
    _ = _ := by rw [denominator_mul_abscissa, div_mul_cancel₀ _ (tripleDen_ne_zero hx hg)]

private theorem gap_ne_zero {t : K} (hq : t + 2 ≠ 0) : 3 * tripleDen t - tripleNum t ≠ 0 := by
  rw [abscissa_gap]
  exact mul_ne_zero (numeral_ne_zero 7 (by decide)) hq

private theorem gap_to_rotated {x : K} (hD : tripleDen (x ^ 3) ≠ 0) :
    3 * x - tripleX x = x * ((3 * tripleDen (x ^ 3) - tripleNum (x ^ 3)) / tripleDen (x ^ 3)) := by
  unfold tripleX
  field_simp [hD] <;> ring

private theorem gap_to_original {x : K} (hD : tripleDen (x ^ 3) ≠ 0) :
    tripleX x - x = x * ((tripleNum (x ^ 3) - tripleDen (x ^ 3)) / tripleDen (x ^ 3)) := by
  unfold tripleX
  field_simp [hD] <;> ring

theorem abscissas_distinct {x : K} (hx : x ≠ 0) (hg : x ^ 3 + 4 ≠ 0) (hq : x ^ 3 + 2 ≠ 0) :
    3 * x ≠ tripleX x := by
  apply sub_ne_zero.mp
  rw [gap_to_rotated (tripleDen_ne_zero hx hg)]
  exact mul_ne_zero hx (div_ne_zero (gap_ne_zero hq) (tripleDen_ne_zero hx hg))

private theorem thirdSlope_normalized {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hg : x ^ 3 + 4 ≠ 0) (he : y ^ 2 = x ^ 3 + 1) :
    thirdSlope 1 x y = (y / x) * (tripleSlopeNum (x ^ 3) / (6 * (x ^ 3 + 1) * (x ^ 3 + 4))) := by
  have h₂ : (2 : K) ≠ 0 := numeral_ne_zero 2 (by decide)
  have h₃ : (3 : K) ≠ 0 := numeral_ne_zero 3 (by decide)
  have h₆ : (6 : K) ≠ 0 := numeral_ne_zero 6 (by decide)
  have hS : x ^ 3 + 1 ≠ 0 := he ▸ pow_ne_zero 2 hy
  calc
    _ = (y / x) * (8 * y ^ 2 / (3 * (x ^ 3 + 4)) - 3 * x ^ 3 / (2 * y ^ 2)) := by
      unfold thirdSlope
      simp only [mul_one]
      field_simp [h₂, h₃, hx, hy, hg] <;> ring
    _ = _ := by
      rw [he]
      unfold tripleSlopeNum
      field_simp [h₂, h₃, h₆, hx, hg, hS] <;> ring

private theorem cancel_slope_factors (t : K) (hs : t + 1 ≠ 0) (hg : t + 4 ≠ 0)
    (hQ : 3 * tripleDen t - tripleNum t ≠ 0) :
    (tripleSlopeNum t / (6 * (t + 1) * (t + 4))) *
      ((tripleNum t - tripleDen t) / (3 * tripleDen t - tripleNum t)) = secantNum t / (t + 4) := by
  have h₆ : (6 : K) ≠ 0 := numeral_ne_zero 6 (by decide)
  let Q := 3 * tripleDen t - tripleNum t
  have hd : (6 * (t + 1) * (t + 4)) * Q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h₆ hs) hg) hQ
  calc
    _ = (tripleSlopeNum t * (tripleNum t - tripleDen t)) /
        ((6 * (t + 1) * (t + 4)) * Q) := by
      simp only [Q, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = secantNum t / (t + 4) := by
      rw [secant_slope_identity t]
      apply (eq_div_iff hg).mpr
      rw [div_mul_eq_mul_div₀]
      apply (div_eq_iff hd).mpr
      change (6 * (t + 1) * Q * secantNum t) * (t + 4) =
        secantNum t * ((6 * (t + 1) * (t + 4)) * Q)
      ring

set_option maxHeartbeats 1000000 in
theorem lastSlope_correct {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hg : x ^ 3 + 4 ≠ 0) (hq : x ^ 3 + 2 ≠ 0) (he : y ^ 2 = x ^ 3 + 1) :
    (-y - tripleY x y) / (3 * x - tripleX x) = lastSlope x y := by
  let t := x ^ 3
  have hD := tripleDen_ne_zero hx hg
  have hQ := gap_ne_zero hq
  have hs : t + 1 ≠ 0 := he ▸ pow_ne_zero 2 hy
  have h₆ : (6 : K) ≠ 0 := numeral_ne_zero 6 (by decide)
  have hv : -y - tripleY x y = thirdSlope 1 x y * (tripleX x - x) := by unfold tripleY; ring
  rw [hv, gap_to_original hD, gap_to_rotated hD, thirdSlope_normalized hx hy hg he]
  calc
    _ = (y / x) * ((tripleSlopeNum t / (6 * (t + 1) * (t + 4))) *
        ((tripleNum t - tripleDen t) / (3 * tripleDen t - tripleNum t))) := by
      change ((y / x) * (tripleSlopeNum t / (6 * (t + 1) * (t + 4))) *
        (x * ((tripleNum t - tripleDen t) / tripleDen t))) /
        (x * ((3 * tripleDen t - tripleNum t) / tripleDen t)) = _
      let b := (y / x) * (tripleSlopeNum t / (6 * (t + 1) * (t + 4)))
      let r := (tripleNum t - tripleDen t) / tripleDen t
      let w := (3 * tripleDen t - tripleNum t) / tripleDen t
      calc
        _ = (x * (b * r)) / (x * w) := by congr 1; ring
        _ = _ := by
          rw [mul_div_mul_left _ _ hx]
          change (b * r) / w = _
          rw [mul_div_assoc]
          change b * (((tripleNum t - tripleDen t) / tripleDen t) /
            ((3 * tripleDen t - tripleNum t) / tripleDen t)) = _
          rw [div_div_div_cancel_right₀ hD]
          dsimp only [b]
          ring
    _ = _ := by
      change _ = (y / x) * (secantNum t / (t + 4))
      rw [cancel_slope_factors t hs hg hQ]

set_option maxHeartbeats 1000000 in
theorem last_abscissa {x y : K} (hx : x ≠ 0) (hg : x ^ 3 + 4 ≠ 0)
    (he : y ^ 2 = x ^ 3 + 1) :
    lastSlope x y ^ 2 - 3 * x - tripleX x = 9 * x ^ 13 := by
  let t := x ^ 3
  have hD : tripleDen t ≠ 0 := tripleDen_ne_zero hx hg
  have h9 : (9 : K) ≠ 0 := numeral_ne_zero 9 (by decide)
  have hm : lastSlope x y ^ 2 = x * (9 * (t + 1) * secantNum t ^ 2 / tripleDen t) := by
    calc
      _ = y ^ 2 * secantNum t ^ 2 / (x ^ 2 * (t + 4) ^ 2) := by
        unfold lastSlope
        rw [mul_pow, div_pow, div_pow]
        simp only [t, div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        rw [he]
        dsimp only [tripleDen, t]
        field_simp [hx, hg, h9] <;> ring
  have hN : 9 * (t + 1) * secantNum t ^ 2 / tripleDen t - 3 - tripleNum t / tripleDen t =
      9 * t ^ 4 := by
    apply mul_right_cancel₀ hD
    calc
      _ = 9 * (t + 1) * secantNum t ^ 2 - 3 * tripleDen t - tripleNum t := by
        field_simp [hD] <;> ring
      _ = _ := secant_abscissa_identity t
  calc
    _ = x * (9 * (t + 1) * secantNum t ^ 2 / tripleDen t - 3 - tripleNum t / tripleDen t) := by
      rw [hm]
      unfold tripleX
      change x * (9 * (t + 1) * secantNum t ^ 2 / tripleDen t) - 3 * x -
        x * (tripleNum t / tripleDen t) = _
      ring
    _ = _ := by rw [hN]; dsimp only [t]; ring

theorem last_ordinate {x y : K} (hx : x ≠ 0) (hg : x ^ 3 + 4 ≠ 0)
    (he : y ^ 2 = x ^ 3 + 1) :
    lastSlope x y * (3 * x - 9 * x ^ 13) + y = -(y ^ 13) := by
  let t := x ^ 3
  have hN : 1 - (secantNum t / (t + 4)) * (9 * t ^ 4 - 3) = -(t + 1) ^ 6 := by
    apply mul_right_cancel₀ (show t + 4 ≠ 0 from hg)
    calc
      _ = t + 4 - ((secantNum t / (t + 4)) * (t + 4)) * (9 * t ^ 4 - 3) := by ring
      _ = t + 4 - secantNum t * (9 * t ^ 4 - 3) := by
        rw [div_mul_cancel₀ _ (show t + 4 ≠ 0 from hg)]
      _ = _ := by linear_combination secant_ordinate_identity t
  calc
    _ = y * (1 - (secantNum t / (t + 4)) * (9 * t ^ 4 - 3)) := by
      unfold lastSlope
      dsimp only [t]
      field_simp [hx, hg] <;> ring
    _ = _ := by rw [hN]; dsimp only [t]; rw [← he]; ring

end
end ManuscriptAudit.Paper5OrdinaryThirteenSecant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenSecant.tripleX_correct,
      ``ManuscriptAudit.Paper5OrdinaryThirteenSecant.abscissas_distinct,
      ``ManuscriptAudit.Paper5OrdinaryThirteenSecant.lastSlope_correct,
      ``ManuscriptAudit.Paper5OrdinaryThirteenSecant.last_abscissa,
      ``ManuscriptAudit.Paper5OrdinaryThirteenSecant.last_ordinate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
