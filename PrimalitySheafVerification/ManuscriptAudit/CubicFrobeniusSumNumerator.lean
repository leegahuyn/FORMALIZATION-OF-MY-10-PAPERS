import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferenceNumerator

/-! The rational secant numerator for the sum of a point with its relative Frobenius. -/

namespace ManuscriptAudit.CubicFrobeniusSumNumerator

open Polynomial CubicFrobeniusDifferenceNumerator

noncomputable section

variable {R : Type*} [Field R]

/-- The sum and difference numerators differ exactly by the cross-term. -/
def sumNumerator (q k : ℕ) (A : R) : R[X] :=
  numerator q k A - C 4 * (X ^ 3 + C A) ^ (k + 1)

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]

theorem sum_chord_identity {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (A : K) (x y : L) (h : y ^ 2 = x ^ 3 + algebraMap K L A) :
    (y ^ Fintype.card K - y) ^ 2 -
        (x ^ Fintype.card K + x) * (x ^ Fintype.card K - x) ^ 2 =
      (sumNumerator (Fintype.card K) k (algebraMap K L A)).eval x := by
  let q := Fintype.card K
  have hCross : y ^ q * y = (x ^ 3 + algebraMap K L A) ^ (k + 1) := by
    rw [← pow_succ y q]
    have he : q + 1 = 2 * (k + 1) := by dsimp only [q]; omega
    rw [he, pow_mul, h]
  simp only [sumNumerator, eval_sub, eval_mul, eval_C, eval_add, eval_pow, eval_X]
  rw [← chord_identity K L hq A x y h, ← hCross]
  ring

/-- Clearing either secant quotient gives the previously proved numerator evaluations. -/
theorem secant_ratios {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (A : K) (x y : L) (h : y ^ 2 = x ^ 3 + algebraMap K L A)
    (hx : x ^ Fintype.card K ≠ x) :
    (((y ^ Fintype.card K - y) / (x ^ Fintype.card K - x)) ^ 2 -
        x ^ Fintype.card K - x =
      (sumNumerator (Fintype.card K) k (algebraMap K L A)).eval x /
        (x ^ Fintype.card K - x) ^ 2) ∧
    (((y ^ Fintype.card K + y) / (x ^ Fintype.card K - x)) ^ 2 -
        x ^ Fintype.card K - x =
      (numerator (Fintype.card K) k (algebraMap K L A)).eval x /
        (x ^ Fintype.card K - x) ^ 2) := by
  let d := x ^ Fintype.card K - x
  have hd := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  have hClear (z : L) :
      ((z / d) ^ 2 - x ^ Fintype.card K - x) * d ^ 2 =
        z ^ 2 - (x ^ Fintype.card K + x) * d ^ 2 := by
    rw [div_pow, sub_mul, sub_mul, div_mul_cancel₀ _ hd]
    ring
  constructor
  · apply (eq_div_iff hd).mpr
    rw [hClear]
    exact sum_chord_identity K L hq A x y h
  · apply (eq_div_iff hd).mpr
    rw [hClear]
    exact chord_identity K L hq A x y h

end

end ManuscriptAudit.CubicFrobeniusSumNumerator

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicFrobeniusSumNumerator.sum_chord_identity,
      ``ManuscriptAudit.CubicFrobeniusSumNumerator.secant_ratios] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
