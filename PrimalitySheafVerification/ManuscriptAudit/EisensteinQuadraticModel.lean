import Lean.Util.CollectAxioms
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.EisensteinRotationPowers

/-! The actual quadratic algebra of integral rotation coefficients and its action on native points. -/

namespace ManuscriptAudit.EisensteinQuadraticModel

open EisensteinPowerCongruence EisensteinRotationPowers RotationNormUnit

abbrev Coefficients := QuadraticAlgebra ℤ (-1) (-1)

def pair (a b : ℤ) : Coefficients := ⟨a, b⟩

theorem norm_eq (z : Coefficients) : z.norm = z.re ^ 2 - z.re * z.im + z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

theorem norm_nonneg (z : Coefficients) : 0 ≤ z.norm := by
  rw [norm_eq]
  nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

theorem pair_pow (a b : ℤ) (n : ℕ) :
    pair a b ^ n = pair (coefficients a b n).1 (coefficients a b n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, ih]
      apply QuadraticAlgebra.ext <;>
        simp [pair, coefficients, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;> ring

theorem norm_pow_sub_one (a b : ℤ) (q : ℕ) (hq : a ^ 2 - a * b + b ^ 2 = (q : ℤ))
    (n : ℕ) :
    ((pair a b) ^ n - 1).norm = ((q ^ n : ℕ) : ℤ) + 1 -
      Paper5PrintedRecurrence.recurrence q (2 * a - b) n := by
  rw [pair_pow, norm_eq]
  simpa only [pair, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, sub_zero] using
    difference_norm_eq_count a b q hq n

/-- A coefficientwise congruence to the identity is scalar divisibility in the integral algebra. -/
theorem sq_dvd_pair_sub_one (m : ℕ) (a b : ℤ)
    (ha : (m : ℤ) ^ 2 ∣ a - 1) (hb : (m : ℤ) ^ 2 ∣ b) :
    (m : Coefficients) ^ 2 ∣ pair a b - 1 := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  refine ⟨pair c d, ?_⟩
  rw [← Nat.cast_pow]
  apply QuadraticAlgebra.ext
  · simp only [pair, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_one,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
      zero_mul, mul_zero, add_zero]
    simpa only [Nat.cast_pow] using hc
  · simp only [pair, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_one,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
      zero_mul, mul_zero, add_zero, sub_zero]
    simpa only [Nat.cast_pow] using hd

/-- Evaluating the literal algebra generator at an actual rotation gives its point operation. -/
def action {R : Type*} [Ring R] (r : R) (hr : r ^ 2 + r + 1 = 0) :
    Coefficients →ₐ[ℤ] R := QuadraticAlgebra.lift ⟨r, by
  have h : r ^ 2 = -1 - r := by
    calc
      r ^ 2 = (r ^ 2 + r + 1) - 1 - r := by abel
      _ = _ := by rw [hr, zero_sub]
  rw [← pow_two, h]
  simp [sub_eq_add_neg]⟩

theorem action_pair {R : Type*} [Ring R] (r : R) (hr : r ^ 2 + r + 1 = 0) (a b : ℤ) :
    action r hr (pair a b) = combination r a b := rfl

theorem action_eq_combination {R : Type*} [Ring R] (r : R) (hr : r ^ 2 + r + 1 = 0)
    (z : Coefficients) : action r hr z = combination r z.re z.im := rfl

/-- An element congruent to one modulo l has norm prime to l. -/
theorem norm_one_add_cast_mod (l : ℕ) (z : Coefficients) :
    ((1 + (l : Coefficients) * z).norm : ZMod l) = 1 := by
  have hr : (1 + (l : Coefficients) * z).re = 1 + (l : ℤ) * z.re := by
    simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_one]
  have hi : (1 + (l : Coefficients) * z).im = (l : ℤ) * z.im := by
    simp [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_one]
  simp only [norm_eq, hr, hi, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_one, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero, zero_pow two_ne_zero,
    one_pow, mul_zero, sub_zero]

end ManuscriptAudit.EisensteinQuadraticModel

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.EisensteinQuadraticModel.norm_nonneg,
      ``ManuscriptAudit.EisensteinQuadraticModel.norm_pow_sub_one,
      ``ManuscriptAudit.EisensteinQuadraticModel.sq_dvd_pair_sub_one,
      ``ManuscriptAudit.EisensteinQuadraticModel.action,
      ``ManuscriptAudit.EisensteinQuadraticModel.action_eq_combination,
      ``ManuscriptAudit.EisensteinQuadraticModel.norm_one_add_cast_mod] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
