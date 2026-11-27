import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferenceNumerator

/-! The derivative distinguishes single and double cancellation in the Frobenius difference. -/

namespace ManuscriptAudit.CubicFrobeniusDifferenceDerivative

open Polynomial CubicFrobeniusDifferenceNumerator

variable (K : Type*) [Field K] [Fintype K]

/-- At rational abscissas the derivative has the same quadratic character factor. -/
theorem eval_derivative {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (A x : K) :
    ((numerator (Fintype.card K) k A).derivative).eval x =
      3 * x ^ 2 * (1 + (x ^ 3 + A) ^ k) := by
  let q := Fintype.card K
  have hQ : (q : K) = 0 := FiniteField.cast_card_eq_zero K
  have hPow₂ : x ^ (2 * q) = x ^ 2 := by
    rw [mul_comm 2 q, pow_mul, FiniteField.pow_card]
  have hPow₁ : x ^ (q + 1) = x ^ 2 := by
    rw [pow_succ, FiniteField.pow_card, pow_two]
  have hK : (2 : K) * ((k : K) + 1) = 1 := by
    have hNat : 2 * (k + 1) = q + 1 := by dsimp only [q]; omega
    have he := congrArg (fun n : ℕ => (n : K)) hNat
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, hQ, zero_add] using he
  change (numerator q k A).derivative.eval x = _
  simp only [numerator, derivative_add, derivative_C_mul, derivative_C, derivative_X,
    derivative_pow_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_zero, eval_one, add_zero,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hQ, hPow₂, hPow₁]
  linear_combination (3 * x ^ 2 * (x ^ 3 + A) ^ k) * hK

/-- A nonzero nonsquare gives double cancellation at its rational abscissa. -/
theorem nonsquare_root {k : ℕ} (hq : Fintype.card K = 2 * k + 1) {A x : K}
    (hs : (x ^ 3 + A) ^ k = -1) :
    (numerator (Fintype.card K) k A).IsRoot x ∧
      (numerator (Fintype.card K) k A).derivative.IsRoot x := by
  constructor
  · change (numerator (Fintype.card K) k A).eval x = 0
    rw [eval_rational, hs, add_neg_cancel, mul_zero]
  · change (numerator (Fintype.card K) k A).derivative.eval x = 0
    rw [eval_derivative K hq, hs, add_neg_cancel, mul_zero]

/-- A zero ordinate gives a simple root of the numerator in good characteristic. -/
theorem zero_ordinate_simple {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    (h₃ : (3 : K) ≠ 0) {A x : K} (hA : A ≠ 0) (hs : x ^ 3 + A = 0) :
    (numerator (Fintype.card K) k A).IsRoot x ∧
      ¬ (numerator (Fintype.card K) k A).derivative.IsRoot x := by
  have hx : x ≠ 0 := by
    intro he
    apply hA
    simpa only [he, zero_pow (by decide : (3 : ℕ) ≠ 0), zero_add] using hs
  constructor
  · change (numerator (Fintype.card K) k A).eval x = 0
    rw [eval_rational, hs, mul_zero, zero_mul]
  · change (numerator (Fintype.card K) k A).derivative.eval x ≠ 0
    rw [eval_derivative K hq, hs, zero_pow hk.ne', add_zero, mul_one]
    exact mul_ne_zero h₃ (pow_ne_zero 2 hx)

end ManuscriptAudit.CubicFrobeniusDifferenceDerivative

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFrobeniusDifferenceDerivative.eval_derivative,
      ``ManuscriptAudit.CubicFrobeniusDifferenceDerivative.nonsquare_root,
      ``ManuscriptAudit.CubicFrobeniusDifferenceDerivative.zero_ordinate_simple] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
