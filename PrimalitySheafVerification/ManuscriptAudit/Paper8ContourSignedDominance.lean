import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A signed first coefficient remains positive under the explicit k⁻⁵ᐟ² contour difference bound. -/

namespace ManuscriptAudit.Paper8ContourSignedDominance

noncomputable section

def decay (k : ℕ) : ℝ := 1 / ((k : ℝ) ^ 2 * Real.sqrt k)

theorem decay_nonneg (k : ℕ) : 0 ≤ decay k := by
  unfold decay
  positivity

private theorem decay_telescope {k : ℕ} (hk : 2 ≤ k) :
    decay k ≤ (1 / 2 : ℝ) * (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
  let x : ℝ := k
  have hx : 2 ≤ x := by
    change (2 : ℝ) ≤ (k : ℝ)
    exact_mod_cast hk
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hSqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hMain : 2 * (x - 1) ≤ x * Real.sqrt x := by
    by_contra! h
    have hProduct : 0 < (2 * (x - 1) - x * Real.sqrt x) *
        (2 * (x - 1) + x * Real.sqrt x) :=
      mul_pos (sub_pos.mpr h) (add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hx1)
        (mul_nonneg hx0.le hSqrt))
    have hSquare : 0 < (2 * (x - 1)) ^ 2 - (x * Real.sqrt x) ^ 2 := by
      nlinarith only [hProduct]
    rw [mul_pow x (Real.sqrt x) 2, Real.sq_sqrt hx0.le] at hSquare
    nlinarith [mul_nonneg hx0.le (sq_nonneg (x - 2))]
  have hTel : 1 / (x - 1) - 1 / x = 1 / ((x - 1) * x) := by
    field_simp [hx0.ne', hx1.ne'] <;> ring
  change 1 / (x ^ 2 * Real.sqrt x) ≤ _
  change 1 / (x ^ 2 * Real.sqrt x) ≤ (1 / 2 : ℝ) * (1 / (x - 1) - 1 / x)
  rw [hTel, mul_one_div]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hx0 _) (Real.sqrt_pos.2 hx0))
    (mul_pos hx1 hx0)).2
  nlinarith only [mul_le_mul_of_nonneg_right hMain hx0.le]

private theorem finite_telescope (start : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + start) - 1 / ((n : ℝ) + start + 1))) =
      1 / start - 1 / ((N : ℝ) + start) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ]
      have h : (N : ℝ) + 1 + start = (N : ℝ) + start + 1 := by ring
      rw [h]
      ring

private theorem finite_tail_bound (t N : ℕ) (ht : 2 ≤ t) :
    (∑ n ∈ Finset.range N, decay (n + t)) ≤ (1 / 2 : ℝ) / ((t : ℝ) - 1) := by
  have htR : 2 ≤ (t : ℝ) := by exact_mod_cast ht
  calc
    _ ≤ ∑ n ∈ Finset.range N, (1 / 2 : ℝ) *
        (1 / ((n : ℝ) + ((t : ℝ) - 1)) - 1 / ((n : ℝ) + ((t : ℝ) - 1) + 1)) := by
      apply Finset.sum_le_sum
      intro n _
      have hN : 2 ≤ n + t := by omega
      have h := decay_telescope hN
      rw [Nat.cast_add] at h
      have h₁ : (n : ℝ) + (t : ℝ) - 1 = (n : ℝ) + ((t : ℝ) - 1) := by ring
      have h₂ : (n : ℝ) + (t : ℝ) - 1 + 1 = (n : ℝ) + (t : ℝ) := by ring
      rw [← h₁, h₂]
      exact h
    _ = (1 / 2 : ℝ) * (1 / ((t : ℝ) - 1) - 1 / ((N : ℝ) + ((t : ℝ) - 1))) := by
      rw [← Finset.mul_sum, finite_telescope]
    _ ≤ _ := by
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
      have h : 0 ≤ 1 / ((N : ℝ) + ((t : ℝ) - 1)) :=
        div_nonneg zero_le_one (by linarith)
      rw [← mul_one_div (1 / 2 : ℝ) ((t : ℝ) - 1)]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ h) (by norm_num)

theorem decay_tail_summable (t : ℕ) (ht : 2 ≤ t) : Summable (fun n => decay (n + t)) :=
  summable_of_sum_range_le (fun _ => decay_nonneg _) (fun N => finite_tail_bound t N ht)

theorem decay_tail_two_lt :
    (∑' n : ℕ, decay (n + 2)) < 1 / 2 := by
  have hSum := decay_tail_summable 2 (by decide)
  have hTail : (∑' n : ℕ, decay (n + 3)) ≤ 1 / 4 := by
    apply Real.tsum_le_of_sum_range_le (fun _ => decay_nonneg _)
    intro N
    convert finite_tail_bound 3 N (by decide) using 1 <;> norm_num
  have hTwo : decay 2 < 1 / 4 := by
    unfold decay
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
    have hSqrt : 1 < Real.sqrt 2 := by
      exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by norm_num)
    exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  rw [hSum.tsum_eq_zero_add]
  change decay 2 + (∑' n : ℕ, decay (n + 3)) < 1 / 2
  linarith

theorem signed_coefficient_pos (delta : ℕ → ℝ) (weights : ℕ → ℂ)
    (hFirst : 0 < delta 1) (hDelta : ∀ k, 0 ≤ delta k)
    (hScale : ∀ k, 2 ≤ k → delta k ≤ decay k * delta 1)
    (hWeightOne : weights 1 = 1) (hWeight : ∀ k, 2 ≤ k → ‖weights k‖ ≤ 2) :
    Summable (fun n : ℕ => weights (n + 1) * (delta (n + 1) : ℂ)) ∧
      0 < (∑' n : ℕ, weights (n + 1) * (delta (n + 1) : ℂ)).re := by
  let T : ℕ → ℂ := fun n => weights (n + 1) * (delta (n + 1) : ℂ)
  have hMaj : Summable (fun n => (2 * delta 1) * decay (n + 2)) :=
    (decay_tail_summable 2 (by decide)).mul_left _
  have hNorm (n : ℕ) : ‖T (n + 1)‖ ≤ (2 * delta 1) * decay (n + 2) := by
    have hn : 2 ≤ n + 2 := by omega
    change ‖weights (n + 2) * (delta (n + 2) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hDelta _)]
    calc
      _ ≤ 2 * (decay (n + 2) * delta 1) :=
        mul_le_mul (hWeight _ hn) (hScale _ hn) (hDelta _) (by norm_num)
      _ = _ := by ring
  have hAbs : Summable (fun n => ‖T (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hNorm hMaj
  have hSum : Summable T := (summable_nat_add_iff 1).mp hAbs.of_norm
  have hBound : ‖∑' n : ℕ, T (n + 1)‖ < delta 1 := by
    calc
      _ ≤ ∑' n : ℕ, ‖T (n + 1)‖ := norm_tsum_le_tsum_norm hAbs
      _ ≤ ∑' n : ℕ, (2 * delta 1) * decay (n + 2) := hAbs.tsum_le_tsum hNorm hMaj
      _ = (2 * delta 1) * (∑' n : ℕ, decay (n + 2)) := tsum_mul_left
      _ < (2 * delta 1) * (1 / 2 : ℝ) :=
        mul_lt_mul_of_pos_left decay_tail_two_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hFirst)
      _ = _ := by ring
  have hZero : T 0 = (delta 1 : ℂ) := by simp [T, hWeightOne]
  refine ⟨hSum, ?_⟩
  change 0 < (∑' n : ℕ, T n).re
  rw [hSum.tsum_eq_zero_add, hZero, Complex.add_re, Complex.ofReal_re]
  have hRe : -‖∑' n : ℕ, T (n + 1)‖ ≤ (∑' n : ℕ, T (n + 1)).re :=
    (neg_le_neg (Complex.abs_re_le_norm _)).trans (neg_abs_le _)
  linarith

end
end ManuscriptAudit.Paper8ContourSignedDominance

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourSignedDominance.decay_tail_summable,
      ``ManuscriptAudit.Paper8ContourSignedDominance.decay_tail_two_lt,
      ``ManuscriptAudit.Paper8ContourSignedDominance.signed_coefficient_pos] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
