import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.NormNum

/-!
# The Euler product with a common formal parameter

Paper 5, p. 171, §7.2 takes all the reciprocal quadratic local factors
with the same formal parameter. For every sequence of nonzero prime
parameters, at least one of degrees one and two fails to stabilize.
-/

namespace ManuscriptAudit.CommonParameterEuler

open PowerSeries

noncomputable section

private def denominator (a p : ℤ) : PowerSeries ℤ :=
  1 - C a * X + C p * X ^ 2

private theorem denominator_constant (a p : ℤ) :
    constantCoeff (denominator a p) = 1 := by
  simp [denominator]

private theorem denominator_first (a p : ℤ) :
    coeff 1 (denominator a p) = -a := by
  simp only [denominator, map_add, map_sub, coeff_C_mul, coeff_one, coeff_X, coeff_X_pow] <;> norm_num

private theorem denominator_second (a p : ℤ) :
    coeff 2 (denominator a p) = p := by
  simp only [denominator, map_add, map_sub, coeff_C_mul, coeff_one, coeff_X, coeff_X_pow] <;> norm_num

/-- Products over the first n factors, in increasing enumeration order. -/
def partialProduct (trace prime : ℕ → ℤ) : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => partialProduct trace prime n * (denominator (trace n) (prime n)).invOfUnit 1

@[simp] private theorem partial_constant (trace prime : ℕ → ℤ) (n : ℕ) :
    constantCoeff (partialProduct trace prime n) = 1 := by
  induction n with
  | zero => simp [partialProduct]
  | succ n ih =>
      simp [partialProduct, ih]

private theorem partial_cancel (trace prime : ℕ → ℤ) (n : ℕ) :
    partialProduct trace prime (n + 1) * denominator (trace n) (prime n) =
      partialProduct trace prime n := by
  have hc : constantCoeff (denominator (trace n) (prime n)) =
      ((1 : ℤˣ) : ℤ) := denominator_constant (trace n) (prime n)
  rw [partialProduct, mul_assoc, PowerSeries.invOfUnit_mul _ _ hc, mul_one]

/-- Successive partial products differ in degree one or two, regardless of the trace. -/
theorem paper5_adjacent_partial_products_change (trace prime : ℕ → ℤ)
    (n : ℕ) (hn : prime n ≠ 0) :
    ¬ (coeff 1 (partialProduct trace prime (n + 1)) = coeff 1 (partialProduct trace prime n) ∧
       coeff 2 (partialProduct trace prime (n + 1)) = coeff 2 (partialProduct trace prime n)) := by
  rintro ⟨h₁, h₂⟩
  have h := congrArg (coeff 1) (partial_cancel trace prime n)
  rw [coeff_one_mul, denominator_constant, denominator_first, partial_constant,
    mul_one, mul_one, h₁] at h
  have ha : trace n = 0 := by omega
  have h := congrArg (coeff 2) (partial_cancel trace prime n)
  have hant : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  have h02 : (0, 2) ∉ ({(1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by decide
  have h11 : (1, 1) ∉ ({(2, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [coeff_mul, hant, Finset.sum_insert h02, Finset.sum_insert h11,
    Finset.sum_singleton] at h
  simp only [coeff_zero_eq_constantCoeff_apply, denominator_constant, denominator_first,
    denominator_second, partial_constant, ha, neg_zero, mul_zero, one_mul, mul_one,
    add_zero, h₂] at h
  exact hn (by omega)

/-- The common-parameter Euler product has no coefficientwise formal limit.
A limit would make both degree-one and degree-two coefficients eventually
constant. This applies to any infinite enumeration of the good primes. -/
theorem paper5_common_parameter_euler_product_fails (trace prime : ℕ → ℤ)
    (hp : ∀ n, prime n ≠ 0) :
    ¬ (∃ f : PowerSeries ℤ, ∀ d : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      coeff d (partialProduct trace prime n) = coeff d f) := by
  rintro ⟨f, hl⟩
  obtain ⟨N₁, h₁⟩ := hl 1
  obtain ⟨N₂, h₂⟩ := hl 2
  let n := max N₁ N₂
  have hn₁ : N₁ ≤ n := le_max_left _ _
  have hn₂ : N₂ ≤ n := le_max_right _ _
  have hs₁ := h₁ (n + 1) (hn₁.trans (Nat.le_succ _))
  have hs₂ := h₂ (n + 1) (hn₂.trans (Nat.le_succ _))
  exact paper5_adjacent_partial_products_change trace prime n (hp n)
    ⟨hs₁.trans (h₁ n hn₁).symm, hs₂.trans (h₂ n hn₂).symm⟩

end

end ManuscriptAudit.CommonParameterEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CommonParameterEuler.paper5_adjacent_partial_products_change,
      ``ManuscriptAudit.CommonParameterEuler.paper5_common_parameter_euler_product_fails] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
