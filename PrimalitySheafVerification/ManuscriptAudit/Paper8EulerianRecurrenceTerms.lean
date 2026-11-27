import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplex

/-! Finite product and coefficient recurrences for the Eulerian partial-theta identity. -/

namespace ManuscriptAudit.Paper8EulerianRecurrenceTerms

noncomputable section

def triangular (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (j + 1)

def product (q a : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, (1 + a * q ^ (j + 1))

def term (q a : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * a ^ (2 * n) * q ^ triangular n / product q a n

theorem triangular_succ (n : ℕ) : triangular (n + 1) = triangular n + (n + 1) := by
  simp only [triangular, Finset.sum_range_succ]

theorem triangular_formula (n : ℕ) : triangular n = n * (n + 1) / 2 := by
  have h (k : ℕ) : 2 * triangular k = k * (k + 1) := by
    induction k with
    | zero => simp [triangular]
    | succ k ih => rw [triangular_succ, mul_add, ih]; ring
  have h' := h n
  omega

theorem le_triangular (n : ℕ) : n ≤ triangular n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => rw [triangular_succ]; omega

theorem product_ge_one {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (n : ℕ) :
    1 ≤ product q a n :=
  Finset.one_le_prod fun j _ => le_add_of_nonneg_right (mul_nonneg ha (pow_nonneg hq _))

theorem product_succ (q a : ℝ) (n : ℕ) :
    product q a (n + 1) = product q a n * (1 + a * q ^ (n + 1)) := by
  simp only [product, Finset.prod_range_succ]

theorem product_head (q a : ℝ) (n : ℕ) :
    product q a (n + 1) = (1 + a * q) * product q (a * q) n := by
  unfold product
  rw [Finset.prod_range_succ', Nat.zero_add, pow_one, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [pow_succ' q (j + 1)]
  ring

theorem term_zero (q a : ℝ) : term q a 0 = 1 := by simp [term, triangular, product]

theorem adjacent_term {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (n : ℕ) :
    (1 + a * q ^ (n + 1)) * term q a (n + 1) = -a ^ 2 * q ^ (n + 1) * term q a n := by
  have hProd : product q a n ≠ 0 := (zero_lt_one.trans_le (product_ge_one hq ha n)).ne'
  have hFactor : 1 + a * q ^ (n + 1) ≠ 0 := by positivity
  unfold term
  rw [product_succ, triangular_succ, pow_succ (-1 : ℝ) n,
    show 2 * (n + 1) = 2 * n + 2 by ring,
    pow_add a (2 * n) 2, pow_add q (triangular n) (n + 1)]
  field_simp [hProd, hFactor] <;> ring

theorem shifted_term {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (n : ℕ) :
    (1 + a * q) * (q ^ (n + 1) * term q a (n + 1)) = -(a ^ 2 * q ^ 2) * term q (a * q) n := by
  have hProd : product q (a * q) n ≠ 0 :=
    (zero_lt_one.trans_le (product_ge_one hq (mul_nonneg ha hq) n)).ne'
  have hFactor : 1 + a * q ≠ 0 := by positivity
  unfold term
  rw [product_head, triangular_succ, pow_succ (-1 : ℝ) n,
    show 2 * (n + 1) = 2 * n + 2 by ring,
    pow_add a (2 * n) 2, pow_add q (triangular n) (n + 1), mul_pow,
    show 2 * n = n + n by ring, pow_add q n n, pow_succ q n]
  field_simp [hProd, hFactor] <;> ring

theorem term_norm_le {q a : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (n : ℕ) : ‖term q a n‖ ≤ q ^ n := by
  have hProd := product_ge_one hq ha n
  have hA : a ^ (2 * n) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ ha ha₁ (2 * n)
  simp only [term, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg hq, abs_of_nonneg ha, abs_of_nonneg (zero_le_one.trans hProd)]
  calc
    _ ≤ a ^ (2 * n) * q ^ triangular n := div_le_self (by positivity) hProd
    _ ≤ 1 * q ^ n := mul_le_mul hA (pow_le_pow_of_le_one hq h₁ (le_triangular n))
      (pow_nonneg hq _) zero_le_one
    _ = _ := one_mul _

end
end ManuscriptAudit.Paper8EulerianRecurrenceTerms

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EulerianRecurrenceTerms.triangular_formula,
      ``ManuscriptAudit.Paper8EulerianRecurrenceTerms.product_head,
      ``ManuscriptAudit.Paper8EulerianRecurrenceTerms.adjacent_term,
      ``ManuscriptAudit.Paper8EulerianRecurrenceTerms.shifted_term,
      ``ManuscriptAudit.Paper8EulerianRecurrenceTerms.term_norm_le] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
