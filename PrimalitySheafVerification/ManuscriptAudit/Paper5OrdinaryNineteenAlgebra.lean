import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicTripleAbscissa

/-! Polynomial certificates for the characteristic-nineteen split cubic. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenAlgebra

open CubicTripleAbscissa

noncomputable section

variable {K : Type*} [Field K] [CharP K 19]

theorem nineteen_zero : (19 : K) = 0 := by
  simpa only [Nat.cast_ofNat] using CharP.cast_eq_zero K 19

theorem numeral_ne_zero (n : ℕ) (h : ¬19 ∣ n) : (n : K) ≠ 0 := by
  rwa [ne_eq, CharP.cast_eq_zero_iff K 19 n]

theorem rotation_cube : (7 : K) ^ 3 = 1 := by
  linear_combination (18 : K) * (nineteen_zero (K := K))

theorem rotation_square : (7 : K) ^ 2 = 11 := by
  linear_combination (2 : K) * (nineteen_zero (K := K))

theorem rotation_ne_one : (7 : K) ≠ 1 := by
  intro h
  exact numeral_ne_zero 6 (by decide) (by linear_combination h)

def tripleNumerator (t : K) : K := t ^ 3 - t ^ 2 + 10 * t + 7

def tripleDenominator (t : K) : K := 9 * t * (t + 4) ^ 2

def rotatedDoubleNumerator (t : K) : K := 7 - 8 * t

def doubleDenominator (t : K) : K := 4 * (t + 1)

def doubleOrdinateNumerator (t : K) : K := t ^ 2 + t - 8

def doubleOrdinateDenominator (t : K) : K := 8 * (t + 1) ^ 2

def thirdSlopeNumerator (t : K) : K := 7 * t ^ 2 - 4 * t - 3

def thirdSlopeDenominator (t : K) : K := 6 * (t + 1) * (t + 4)

def lastSlopeNumerator (t : K) : K := -9 - 6 * t + 4 * t ^ 2 - 9 * t ^ 3 + 5 * t ^ 4 - t ^ 5

theorem triple_numerator_eq (x : K) : numerator 1 x = tripleNumerator (x ^ 3) := by
  unfold numerator tripleNumerator
  linear_combination (-5 * (x ^ 3) ^ 2 + 2 * (x ^ 3) + 3) * (nineteen_zero (K := K))

theorem triple_denominator_mul_abscissa (x : K) : denominator 1 x * x = tripleDenominator (x ^ 3) := by
  unfold denominator tripleDenominator
  ring

theorem rotated_double_numerator_eq (t : K) : 11 * (t - 8) = rotatedDoubleNumerator t := by
  unfold rotatedDoubleNumerator
  linear_combination (t - 5) * (nineteen_zero (K := K))

theorem double_ordinate_numerator_eq (t : K) : t ^ 2 + 20 * t - 8 = doubleOrdinateNumerator t := by
  unfold doubleOrdinateNumerator
  linear_combination t * (nineteen_zero (K := K))

theorem third_slope_numerator_eq (t : K) :
    16 * (t + 1) ^ 2 - 9 * t * (t + 4) = thirdSlopeNumerator t := by
  unfold thirdSlopeNumerator
  linear_combination (nineteen_zero (K := K))

def abscissaGap (t : K) : K :=
  rotatedDoubleNumerator t * tripleDenominator t - tripleNumerator t * doubleDenominator t

def tripleOrdinateNumerator (t : K) : K :=
  thirdSlopeNumerator t * (tripleDenominator t - tripleNumerator t) -
    thirdSlopeDenominator t * tripleDenominator t

theorem abscissa_gap (t : K) : abscissaGap t = 9 * (t - 1) := by
  unfold abscissaGap rotatedDoubleNumerator tripleDenominator tripleNumerator doubleDenominator
  linear_combination (-1 + 49 * t - 36 * t ^ 2 - 27 * t ^ 3 - 4 * t ^ 4) * (nineteen_zero (K := K))

set_option maxHeartbeats 800000 in
theorem last_slope_identity (t : K) :
    doubleDenominator t *
      (-doubleOrdinateNumerator t * thirdSlopeDenominator t * tripleDenominator t -
        tripleOrdinateNumerator t * doubleOrdinateDenominator t) =
      6 * doubleOrdinateDenominator t * abscissaGap t * lastSlopeNumerator t := by
  unfold tripleOrdinateNumerator abscissaGap doubleDenominator doubleOrdinateNumerator
    thirdSlopeDenominator tripleDenominator doubleOrdinateDenominator lastSlopeNumerator
    thirdSlopeNumerator tripleNumerator rotatedDoubleNumerator
  linear_combination (-672 + 31840 * t + 86304 * t ^ 2 + 58000 * t ^ 3 + 11136 * t ^ 4 + 7016 * t ^ 5 - 23048 * t ^ 6 - 20008 * t ^ 7 + 5816 * t ^ 8 + 2160 * t ^ 9 - 720 * t ^ 10 - 192 * t ^ 11) *
    (nineteen_zero (K := K))

theorem last_abscissa_identity (t : K) :
    36 * lastSlopeNumerator t ^ 2 - rotatedDoubleNumerator t * tripleDenominator t -
      4 * (t + 1) * tripleNumerator t = 4 * (t + 1) * tripleDenominator t * t ^ 6 := by
  unfold lastSlopeNumerator rotatedDoubleNumerator tripleDenominator tripleNumerator
  linear_combination (152 + 148 * t - 36 * t ^ 2 + 243 * t ^ 3 + 68 * t ^ 4 - 216 * t ^ 5 + 252 * t ^ 6 - 216 * t ^ 7 + 36 * t ^ 8 - 36 * t ^ 9) * (nineteen_zero (K := K))

theorem last_ordinate_identity (t : K) :
    2 * lastSlopeNumerator t * (rotatedDoubleNumerator t - doubleDenominator t * t ^ 6) +
      doubleOrdinateNumerator t * (t + 4) =
      (t + 1) ^ 9 * (t + 4) * doubleOrdinateDenominator t := by
  unfold lastSlopeNumerator rotatedDoubleNumerator doubleDenominator doubleOrdinateNumerator
    doubleOrdinateDenominator
  linear_combination (-10 - 16 * t - 89 * t ^ 2 - 311 * t ^ 3 - 614 * t ^ 4 - 922 * t ^ 5 - 968 * t ^ 6 - 744 * t ^ 7 - 416 * t ^ 8 - 160 * t ^ 9 - 40 * t ^ 10 - 8 * t ^ 11) * (nineteen_zero (K := K))

end
end ManuscriptAudit.Paper5OrdinaryNineteenAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.rotation_cube,
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.rotation_square,
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.rotation_ne_one,
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.triple_numerator_eq,
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.triple_denominator_mul_abscissa,
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.abscissa_gap,
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.last_slope_identity,
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.last_abscissa_identity,
      ``ManuscriptAudit.Paper5OrdinaryNineteenAlgebra.last_ordinate_identity] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
