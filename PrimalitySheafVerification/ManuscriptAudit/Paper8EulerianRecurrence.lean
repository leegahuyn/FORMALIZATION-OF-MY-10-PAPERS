import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianRecurrenceTerms

/-! The genuine one-parameter Eulerian sum satisfies a simple recurrence. -/

namespace ManuscriptAudit.Paper8EulerianRecurrence

open Paper8EulerianRecurrenceTerms

noncomputable section

def H (q a : ℝ) : ℝ := ∑' n : ℕ, term q a n

def weightedTerm (q a : ℝ) (n : ℕ) : ℝ := q ^ n * term q a n

def weighted (q a : ℝ) : ℝ := ∑' n : ℕ, weightedTerm q a n

theorem term_summable {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    Summable (term q a) :=
  (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_norm_le hq h₁.le ha ha₁)
    (summable_geometric_of_lt_one hq h₁)).of_norm

theorem H_abs_le_geometric {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    |H q a| ≤ (1 - q)⁻¹ := by
  simpa only [H, Real.norm_eq_abs] using
    tsum_of_norm_bounded (hasSum_geometric_of_lt_one hq h₁) (term_norm_le hq h₁.le ha ha₁)

private theorem weightedTerm_summable {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1)
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) : Summable (weightedTerm q a) := by
  have hTerm (n : ℕ) : ‖weightedTerm q a n‖ ≤ q ^ n := by
    rw [weightedTerm, norm_mul, Real.norm_of_nonneg (pow_nonneg hq n)]
    have hPow : q ^ n ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hq h₁.le n
    calc
      _ ≤ 1 * ‖term q a n‖ := mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using term_norm_le hq h₁.le ha ha₁ n
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hTerm
    (summable_geometric_of_lt_one hq h₁)).of_norm

theorem H_recurrence {q a : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    H q a = 1 - a ^ 2 * q + a ^ 3 * q ^ 2 * H q (a * q) := by
  have hs := term_summable hq h₁ ha ha₁
  have hw := weightedTerm_summable hq h₁ ha ha₁
  have hsTail : Summable (fun n : ℕ => term q a (n + 1)) := (summable_nat_add_iff 1).mpr hs
  have hwTail : Summable (fun n : ℕ => weightedTerm q a (n + 1)) :=
    (summable_nat_add_iff 1).mpr hw
  have hTail : (∑' n : ℕ, term q a (n + 1)) = H q a - 1 := by
    have h := hs.tsum_eq_zero_add
    rw [term_zero] at h
    unfold H
    linarith only [h]
  have hWeightedTail : (∑' n : ℕ, weightedTerm q a (n + 1)) = weighted q a - 1 := by
    have h := hw.tsum_eq_zero_add
    have hZero : weightedTerm q a 0 = 1 := by simp [weightedTerm, term_zero]
    rw [hZero] at h
    unfold weighted
    linarith only [h]
  have hAdjacent (n : ℕ) :
      term q a (n + 1) + a * weightedTerm q a (n + 1) =
        (-a ^ 2 * q) * weightedTerm q a n := by
    unfold weightedTerm
    have h := adjacent_term hq ha n
    rw [pow_succ' q n] at h ⊢
    linear_combination h
  have hAdjacentSum : tsum (fun n : ℕ => term q a (n + 1) + a * weightedTerm q a (n + 1)) =
      tsum (fun n : ℕ => (-a ^ 2 * q) * weightedTerm q a n) :=
    congrArg (fun f : ℕ → ℝ => tsum f) (funext hAdjacent)
  rw [hsTail.tsum_add (hwTail.mul_left a), hwTail.tsum_mul_left, hw.tsum_mul_left,
    hTail, hWeightedTail] at hAdjacentSum
  have hAQ : a * q ≤ 1 := by
    calc
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left h₁.le ha
      _ ≤ _ := by simpa only [mul_one] using ha₁
  have hsShift := term_summable hq h₁ (mul_nonneg ha hq) hAQ
  have hShift (n : ℕ) :
      (1 + a * q) * weightedTerm q a (n + 1) = -(a ^ 2 * q ^ 2) * term q (a * q) n :=
    shifted_term hq ha n
  have hShiftSum : tsum (fun n : ℕ => (1 + a * q) * weightedTerm q a (n + 1)) =
      tsum (fun n : ℕ => -(a ^ 2 * q ^ 2) * term q (a * q) n) :=
    congrArg (fun f : ℕ → ℝ => tsum f) (funext hShift)
  rw [hwTail.tsum_mul_left, hsShift.tsum_mul_left, hWeightedTail] at hShiftSum
  change H q a - 1 + a * (weighted q a - 1) = (-a ^ 2 * q) * weighted q a at hAdjacentSum
  change (1 + a * q) * (weighted q a - 1) = -(a ^ 2 * q ^ 2) * H q (a * q) at hShiftSum
  linear_combination hAdjacentSum - a * hShiftSum

end
end ManuscriptAudit.Paper8EulerianRecurrence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EulerianRecurrence.term_summable,
      ``ManuscriptAudit.Paper8EulerianRecurrence.H_abs_le_geometric,
      ``ManuscriptAudit.Paper8EulerianRecurrence.H_recurrence] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
