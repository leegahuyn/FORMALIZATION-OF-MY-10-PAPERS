import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenAlgebra

/-! Exact comparison equations for the nonzero characteristic-nineteen torsion coordinates. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenTorsionAlgebra

open Paper5OrdinaryNineteenAlgebra

noncomputable section

variable {K : Type*} [Field K] [CharP K 19]

def torsionCubic (t : K) : K := (t - 2) * (t - 14) * (t - 17)

def singleRotatedDoubleNumerator (t : K) : K := 1 + 7 * t

theorem torsionCubic_eq_zero_iff (t : K) : torsionCubic t = 0 ↔ t = 2 ∨ t = 14 ∨ t = 17 := by
  simp only [torsionCubic, mul_eq_zero, sub_eq_zero, or_assoc]

theorem torsionCubic_nonzero_values {t : K} (ht : torsionCubic t = 0) :
    t ≠ 0 ∧ t + 1 ≠ 0 ∧ t + 4 ≠ 0 := by
  rcases (torsionCubic_eq_zero_iff t).mp ht with rfl | rfl | rfl
  · rw [show (2 : K) + 1 = 3 by ring, show (2 : K) + 4 = 6 by ring]
    exact ⟨numeral_ne_zero 2 (by decide), numeral_ne_zero 3 (by decide),
      numeral_ne_zero 6 (by decide)⟩
  · rw [show (14 : K) + 1 = 15 by ring, show (14 : K) + 4 = 18 by ring]
    exact ⟨numeral_ne_zero 14 (by decide), numeral_ne_zero 15 (by decide),
      numeral_ne_zero 18 (by decide)⟩
  · rw [show (17 : K) + 1 = 18 by ring, show (17 : K) + 4 = 21 by ring]
    exact ⟨numeral_ne_zero 17 (by decide), numeral_ne_zero 18 (by decide),
      numeral_ne_zero 21 (by decide)⟩

theorem rotation_square_times_double (t : K) :
    (11 : K) * rotatedDoubleNumerator t = singleRotatedDoubleNumerator t := by
  unfold rotatedDoubleNumerator singleRotatedDoubleNumerator
  linear_combination (4 - 5 * t) * (nineteen_zero (K := K))

private theorem abscissa_difference (t : K) :
    singleRotatedDoubleNumerator t * tripleDenominator t -
      tripleNumerator t * doubleDenominator t = (9 + 2 * t) * torsionCubic t := by
  unfold singleRotatedDoubleNumerator tripleDenominator tripleNumerator doubleDenominator torsionCubic
  linear_combination (224 - 88 * t + 39 * t ^ 2 + 30 * t ^ 3 + 3 * t ^ 4) * (nineteen_zero (K := K))

private theorem ordinate_difference (t : K) :
    tripleOrdinateNumerator t * doubleOrdinateDenominator t -
      doubleOrdinateNumerator t * (thirdSlopeDenominator t * tripleDenominator t) =
      (3 * (t + 1)) * torsionCubic t := by
  unfold tripleOrdinateNumerator doubleOrdinateDenominator doubleOrdinateNumerator
    thirdSlopeDenominator tripleDenominator thirdSlopeNumerator tripleNumerator torsionCubic
  linear_combination (84 - 112 * t - 3779 * t ^ 2 - 7616 * t ^ 3 - 5377 * t ^ 4 - 1474 * t ^ 5 - 132 * t ^ 6 - 2 * t ^ 7) *
    (nineteen_zero (K := K))

/-- Triple and singly rotated double coordinates agree precisely on the three certified fibers. -/
theorem fractional_coordinates_iff (t : K) (ht : t ≠ 0) (hs : t + 1 ≠ 0) (hg : t + 4 ≠ 0) :
    (tripleNumerator t / tripleDenominator t =
      singleRotatedDoubleNumerator t / doubleDenominator t ∧
      tripleOrdinateNumerator t / (thirdSlopeDenominator t * tripleDenominator t) =
        doubleOrdinateNumerator t / doubleOrdinateDenominator t) ↔ torsionCubic t = 0 := by
  have hD : tripleDenominator t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (numeral_ne_zero 9 (by decide)) ht) (pow_ne_zero _ hg)
  have hU : doubleDenominator t ≠ 0 := mul_ne_zero (numeral_ne_zero 4 (by decide)) hs
  have hV : doubleOrdinateDenominator t ≠ 0 :=
    mul_ne_zero (numeral_ne_zero 8 (by decide)) (pow_ne_zero _ hs)
  have hW : thirdSlopeDenominator t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (numeral_ne_zero 6 (by decide)) hs) hg
  rw [div_eq_div_iff hD hU, div_eq_div_iff (mul_ne_zero hW hD) hV]
  constructor
  · intro h
    have hY := sub_eq_zero.mpr h.2
    rw [ordinate_difference] at hY
    exact (mul_eq_zero.mp hY).resolve_left (mul_ne_zero (numeral_ne_zero 3 (by decide)) hs)
  · intro h
    constructor
    · symm
      apply sub_eq_zero.mp
      rw [abscissa_difference, h, mul_zero]
    · apply sub_eq_zero.mp
      rw [ordinate_difference, h, mul_zero]

end
end ManuscriptAudit.Paper5OrdinaryNineteenTorsionAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionAlgebra.torsionCubic_eq_zero_iff,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionAlgebra.torsionCubic_nonzero_values,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionAlgebra.rotation_square_times_double,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionAlgebra.fractional_coordinates_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
