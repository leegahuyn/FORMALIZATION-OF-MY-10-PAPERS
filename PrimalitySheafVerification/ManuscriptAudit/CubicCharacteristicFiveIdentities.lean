import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.LinearCombination

/-! Polynomial identities for the multiplication-by-five formulas on centered cubics. -/

namespace ManuscriptAudit.CubicCharacteristicFiveIdentities

variable {K : Type*} [CommRing K]

def ordinateFactor (t : K) : K := 2 * t ^ 2 - 1

def fourthAbscissaNumerator (t : K) : K :=
  (t + 2) * (-t * (t + 2) ^ 3 + 2 * (t + 1) ^ 3)

def fourthOrdinateNumerator (t : K) : K :=
  2 * t ^ 2 * (t + 2) ^ 6 - (t + 1) ^ 6

def secantFactor (t : K) : K :=
  -t ^ 6 + 2 * t ^ 5 - 2 * t ^ 3 - t ^ 2 + t - 1

variable [CharP K 5]

private theorem five_zero : (5 : K) = 0 := CharP.cast_eq_zero K 5

theorem fourth_abscissa_difference (t : K) :
    fourthAbscissaNumerator t - (t + 1) * ordinateFactor t ^ 2 = 2 * (t - 1) := by
  unfold fourthAbscissaNumerator ordinateFactor
  linear_combination
    (-t ^ 5 - 2 * t ^ 4 - 2 * t ^ 3 - 2 * t ^ 2 - t + 1) * (five_zero : (5 : K) = 0)

theorem fourth_ordinate_difference (t : K) :
    fourthOrdinateNumerator t - (t + 1) ^ 2 * ordinateFactor t ^ 3 =
      t * (t - 1) * secantFactor t := by
  unfold fourthOrdinateNumerator ordinateFactor secantFactor
  linear_combination
    (-t ^ 8 + t ^ 7 + 25 * t ^ 6 + 68 * t ^ 5 + 94 * t ^ 4 +
      70 * t ^ 3 + 22 * t ^ 2 - t) * (five_zero : (5 : K) = 0)

theorem fifth_abscissa (t : K) :
    t * secantFactor t ^ 2 -
        4 * (fourthAbscissaNumerator t + (t + 1) * ordinateFactor t ^ 2) =
      4 * t ^ 8 * (t + 1) * ordinateFactor t ^ 2 := by
  unfold secantFactor fourthAbscissaNumerator ordinateFactor
  linear_combination
    (-3 * t ^ 13 - 4 * t ^ 12 + 4 * t ^ 11 + 4 * t ^ 10 - 2 * t ^ 9 -
      2 * t ^ 8 + 2 * t ^ 7 - 3 * t ^ 5 + 2 * t ^ 4 + 15 * t ^ 3 +
      14 * t ^ 2 + t - 4) * (five_zero : (5 : K) = 0)

theorem fifth_ordinate (t : K) :
    t * secantFactor t * (1 - t ^ 8) =
      2 * (t + 1) * ordinateFactor t * (1 - (t + 1) ^ 12) := by
  unfold secantFactor ordinateFactor
  linear_combination
    (t ^ 15 + 10 * t ^ 14 + 62 * t ^ 13 + 224 * t ^ 12 + 541 * t ^ 11 +
      915 * t ^ 10 + 1087 * t ^ 9 + 858 * t ^ 8 + 343 * t ^ 7 - 114 * t ^ 6 -
      286 * t ^ 5 - 224 * t ^ 4 - 105 * t ^ 3 - 31 * t ^ 2 - 5 * t) *
        (five_zero : (5 : K) = 0)

end ManuscriptAudit.CubicCharacteristicFiveIdentities

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicCharacteristicFiveIdentities.fourth_abscissa_difference,
      ``ManuscriptAudit.CubicCharacteristicFiveIdentities.fourth_ordinate_difference,
      ``ManuscriptAudit.CubicCharacteristicFiveIdentities.fifth_abscissa,
      ``ManuscriptAudit.CubicCharacteristicFiveIdentities.fifth_ordinate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
