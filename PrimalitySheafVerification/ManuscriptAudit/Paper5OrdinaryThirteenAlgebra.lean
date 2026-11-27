import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicTripleAbscissa

/-! Polynomial identities for the actual characteristic-thirteen secant. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenAlgebra

open CubicTripleAbscissa

noncomputable section

variable {K : Type*} [Field K] [CharP K 13]

theorem thirteen_zero : (13 : K) = 0 := by
  simpa only [Nat.cast_ofNat] using (CharP.cast_eq_zero K 13)

theorem numeral_ne_zero (n : ℕ) (h : ¬13 ∣ n) : (n : K) ≠ 0 := by
  rwa [ne_eq, CharP.cast_eq_zero_iff K 13 n]

theorem rotation_cube : (3 : K) ^ 3 = 1 := by
  linear_combination (2 : K) * (thirteen_zero (K := K))

theorem rotation_ne_one : (3 : K) ≠ 1 := by
  intro h
  exact numeral_ne_zero 2 (by decide) (by linear_combination h)

def tripleNum (t : K) : K := t ^ 3 - 96 * t ^ 2 + 48 * t + 64

def tripleDen (t : K) : K := 9 * t * (t + 4) ^ 2

def secantNum (t : K) : K := 3 * t ^ 3 + 4 * t ^ 2 + 6

def tripleSlopeNum (t : K) : K := 16 * (t + 1) ^ 2 - 9 * t * (t + 4)

theorem numerator_eq (x : K) : numerator 1 x = tripleNum (x ^ 3) := by
  unfold numerator tripleNum
  ring

theorem denominator_mul_abscissa (x : K) : denominator 1 x * x = tripleDen (x ^ 3) := by
  unfold denominator tripleDen
  ring

theorem abscissa_gap (t : K) : 3 * tripleDen t - tripleNum t = 7 * (t + 2) := by
  unfold tripleDen tripleNum
  linear_combination (2 * t ^ 3 + 24 * t ^ 2 + 29 * t - 6) * (thirteen_zero (K := K))

theorem secant_slope_identity (t : K) :
    tripleSlopeNum t * (tripleNum t - tripleDen t) =
      6 * (t + 1) * (3 * tripleDen t - tripleNum t) * secantNum t := by
  unfold tripleSlopeNum tripleNum tripleDen secantNum
  linear_combination (-36 * t ^ 7 - 516 * t ^ 6 - 1592 * t ^ 5 - 1888 * t ^ 4 -
    1448 * t ^ 3 - 1952 * t ^ 2 - 1024 * t + 256) * (thirteen_zero (K := K))

theorem secant_abscissa_identity (t : K) :
    9 * (t + 1) * secantNum t ^ 2 - 3 * tripleDen t - tripleNum t =
      9 * t ^ 4 * tripleDen t := by
  unfold secantNum tripleDen tripleNum
  linear_combination (-27 * t ^ 6 - 72 * t ^ 5 + 36 * t ^ 4 + 56 * t ^ 3 +
    24 * t ^ 2 - 12 * t + 20) * (thirteen_zero (K := K))

theorem secant_ordinate_identity (t : K) :
    (1 + (t + 1) ^ 6) * (t + 4) = secantNum t * (9 * t ^ 4 - 3) := by
  unfold secantNum
  linear_combination (-2 * t ^ 7 - 2 * t ^ 6 + 3 * t ^ 5 + 2 * t ^ 4 + 8 * t ^ 3 +
    6 * t ^ 2 + 2 * t + 2) * (thirteen_zero (K := K))

end
end ManuscriptAudit.Paper5OrdinaryThirteenAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenAlgebra.rotation_cube,
      ``ManuscriptAudit.Paper5OrdinaryThirteenAlgebra.rotation_ne_one,
      ``ManuscriptAudit.Paper5OrdinaryThirteenAlgebra.numerator_eq,
      ``ManuscriptAudit.Paper5OrdinaryThirteenAlgebra.denominator_mul_abscissa,
      ``ManuscriptAudit.Paper5OrdinaryThirteenAlgebra.abscissa_gap,
      ``ManuscriptAudit.Paper5OrdinaryThirteenAlgebra.secant_slope_identity,
      ``ManuscriptAudit.Paper5OrdinaryThirteenAlgebra.secant_abscissa_identity,
      ``ManuscriptAudit.Paper5OrdinaryThirteenAlgebra.secant_ordinate_identity] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
