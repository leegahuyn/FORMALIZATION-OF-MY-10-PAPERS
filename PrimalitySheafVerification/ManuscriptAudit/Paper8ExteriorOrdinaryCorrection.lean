import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorOrdinaryProduct

/-! The literal p. 335 triangular numerator and its two-step recurrence. -/

namespace ManuscriptAudit.Paper8ExteriorOrdinaryCorrection

open Paper8EulerianRecurrenceTerms
open Paper8ExteriorProductCorrection (correctionNumeratorTerm)

noncomputable section

def CTerm (q a : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * a ^ (2 * n) * q ^ triangular n

def C (q a : ℝ) : ℝ := ∑' n : ℕ, CTerm q a n

theorem CTerm_norm_le {q a : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (n : ℕ) : ‖CTerm q a n‖ ≤ q ^ n := by
  have hPowA : a ^ (2 * n) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ ha ha₁ (2 * n)
  simp only [CTerm, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg ha, abs_of_nonneg hq]
  simpa only [one_mul] using
    (mul_le_mul hPowA (pow_le_pow_of_le_one hq h₁ (le_triangular n))
      (pow_nonneg hq _) zero_le_one)

theorem C_summable {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    Summable (CTerm q a) :=
  (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (CTerm_norm_le hq h₁.le ha ha₁)
    (summable_geometric_of_lt_one hq h₁)).of_norm

theorem C_abs_le_geometric {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    |C q a| ≤ (1 - q)⁻¹ := by
  simpa only [C, Real.norm_eq_abs] using
    tsum_of_norm_bounded (hasSum_geometric_of_lt_one hq h₁) (CTerm_norm_le hq h₁.le ha ha₁)

theorem CTerm_two_shift (q a : ℝ) (n : ℕ) :
    CTerm q a (n + 2) = a ^ 4 * q ^ 3 * CTerm q (a * q) n := by
  have hTriangle : triangular (n + 2) = triangular n + (2 * n + 3) := by
    change triangular ((n + 1) + 1) = _
    rw [triangular_succ (n + 1), triangular_succ n]
    ring
  rw [CTerm, CTerm, hTriangle, show 2 * (n + 2) = 2 * n + 4 by ring,
    pow_add a (2 * n) 4, pow_add q (triangular n) (2 * n + 3), pow_add q (2 * n) 3,
    pow_add (-1 : ℝ) n 2, mul_pow]
  ring

theorem C_recurrence {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    C q a = 1 - a ^ 2 * q + a ^ 4 * q ^ 3 * C q (a * q) := by
  have hAQ : a * q ≤ 1 := by
    calc
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left h₁.le ha
      _ ≤ _ := by simpa only [mul_one] using ha₁
  have hSum := C_summable hq h₁ ha ha₁
  have hShift := C_summable hq h₁ (mul_nonneg ha hq) hAQ
  have hSplit : (∑ n ∈ Finset.range 2, CTerm q a n) +
      (∑' n : ℕ, CTerm q a (n + 2)) = C q a :=
    Summable.sum_add_tsum_nat_add 2 hSum
  have hFirst : (∑ n ∈ Finset.range 2, CTerm q a n) = 1 - a ^ 2 * q := by
    norm_num [Finset.sum_range_succ, CTerm, triangular, sub_eq_add_neg]
  have hTail : (∑' n : ℕ, CTerm q a (n + 2)) = a ^ 4 * q ^ 3 * C q (a * q) := by
    simp_rw [CTerm_two_shift]
    exact hShift.tsum_mul_left _
  rw [hFirst, hTail] at hSplit
  exact hSplit.symm

theorem C_one_eq_literal_numerator (q : ℝ) : C q 1 = ∑' n : ℕ, correctionNumeratorTerm q n := by
  simp only [C, CTerm, triangular_formula, one_pow, mul_one, correctionNumeratorTerm]

end
end ManuscriptAudit.Paper8ExteriorOrdinaryCorrection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorOrdinaryCorrection.C_abs_le_geometric,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryCorrection.CTerm_two_shift,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryCorrection.C_recurrence,
      ``ManuscriptAudit.Paper8ExteriorOrdinaryCorrection.C_one_eq_literal_numerator] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
