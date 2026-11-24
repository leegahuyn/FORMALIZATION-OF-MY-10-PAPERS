import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.Spt1

/-!
# The quadratic remainder of the 2-adic logarithm

Paper 1, p. 7, Remark 2.2 states a valuation bound of at least 2k for
the first-order logarithm remainder. At p = 2, k = 2 and input 4,
the quadratic term strictly dominates the rest of the tail. The resulting
norm is 1/8 and the stated bound would require at most 1/16.
-/

namespace ManuscriptAudit.PadicRemainder

open scoped BigOperators
open Spt1.PadicLog

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem shifted_log_geometric_bound (i : ℕ) :
    ((i + 3 : ℕ) : ℝ) * ((1 : ℝ) / 4) ^ (i + 3) ≤ 3 / 64 := by
  induction i with
  | zero => norm_num
  | succ i ih =>
    have hs : i.succ + 3 = (i + 3) + 1 := by omega
    rw [hs, pow_succ, Nat.cast_add, Nat.cast_one]
    have hthree : (3 : ℝ) ≤ ((i + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ i + 3 by omega)
    have hc : (((i + 3 : ℕ) : ℝ) + 1) * (1 / 4) ≤ ((i + 3 : ℕ) : ℝ) := by
      linarith
    calc
      (((i + 3 : ℕ) : ℝ) + 1) * (((1 : ℝ) / 4) ^ (i + 3) * (1 / 4)) =
          ((((i + 3 : ℕ) : ℝ) + 1) * (1 / 4)) * ((1 : ℝ) / 4) ^ (i + 3) := by ring
      _ ≤ ((i + 3 : ℕ) : ℝ) * ((1 : ℝ) / 4) ^ (i + 3) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ 3 / 64 := ih

private theorem norm_two_in_Q2 : ‖(2 : ℚ_[2])‖ = (1 : ℝ) / 2 := by
  simpa [one_div] using (Padic.norm_p (p := 2))

private theorem norm_four_in_Q2 : ‖(4 : ℚ_[2])‖ = (1 : ℝ) / 4 := by
  rw [show (4 : ℚ_[2]) = (2 : ℚ_[2]) ^ 2 by norm_num, norm_pow, norm_two_in_Q2]
  norm_num

private theorem norm_log_quadratic_term_in_Q2 :
    ‖padicLogSeries (4 : ℚ_[2]) 2‖ = (1 : ℝ) / 8 := by
  have hterm : padicLogSeries (4 : ℚ_[2]) 2 = -8 := by
    norm_num [padicLogSeries]
  rw [hterm, norm_neg, show (8 : ℚ_[2]) = (2 : ℚ_[2]) ^ 3 by norm_num, norm_pow,
    norm_two_in_Q2]
  norm_num

private theorem norm_padic_log_remainder_four :
    ‖padicLog1p (4 : ℚ_[2]) - 4‖ = (1 : ℝ) / 8 := by
  let tail : ℚ_[2] := ∑' n : ℕ, padicLogSeries (4 : ℚ_[2]) (n + 3)
  have htail : ‖tail‖ ≤ (3 : ℝ) / 64 := by
    change ‖∑' n : ℕ, padicLogSeries (4 : ℚ_[2]) (n + 3)‖ ≤ (3 : ℝ) / 64
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) ?_
    intro i
    calc
      ‖padicLogSeries (4 : ℚ_[2]) (i + 3)‖ ≤
          ((i + 3 : ℕ) : ℝ) * ‖(4 : ℚ_[2])‖ ^ (i + 3) :=
        padicLogSeries_norm_le _ _
      _ ≤ 3 / 64 := by
        rw [norm_four_in_Q2]
        exact shifted_log_geometric_bound i
  have hsum : Summable (padicLogSeries (4 : ℚ_[2])) :=
    padicLogSeries_summable (by
      rw [norm_four_in_Q2]
      norm_num)
  have hprefix : (∑ i ∈ Finset.range 3, padicLogSeries (4 : ℚ_[2]) i) =
      (4 : ℚ_[2]) + padicLogSeries (4 : ℚ_[2]) 2 := by
    simp [Finset.sum_range_succ, padicLogSeries_zero_term, padicLogSeries_one_term]
  have hsplit : padicLog1p (4 : ℚ_[2]) - 4 = padicLogSeries (4 : ℚ_[2]) 2 + tail := by
    have hh := Summable.sum_add_tsum_nat_add 3 hsum
    rw [hprefix] at hh
    change ((4 : ℚ_[2]) + padicLogSeries (4 : ℚ_[2]) 2) + tail =
      padicLog1p (4 : ℚ_[2]) at hh
    rw [← hh]
    abel
  have hlt : ‖tail‖ < ‖padicLogSeries (4 : ℚ_[2]) 2‖ := htail.trans_lt (by
    rw [norm_log_quadratic_term_in_Q2]
    norm_num)
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
    max_eq_left hlt.le, norm_log_quadratic_term_in_Q2]

/-- Paper 1, p. 7, Remark 2.2. At p = 2 and k = 2, the logarithm remainder
exceeds the printed norm threshold. -/
theorem paper1_padic_log_quadratic_remainder_bound_false :
    ‖(4 : ℚ_[2])‖ = (2 : ℝ) ^ (-2 : ℤ) ∧
      ‖padicLog1p (4 : ℚ_[2]) - 4‖ = (1 : ℝ) / 8 ∧
      (2 : ℝ) ^ (-4 : ℤ) < ‖padicLog1p (4 : ℚ_[2]) - 4‖ := by
  refine ⟨?_, norm_padic_log_remainder_four, ?_⟩
  · rw [norm_four_in_Q2]
    norm_num
  · rw [norm_padic_log_remainder_four]
    norm_num

end ManuscriptAudit.PadicRemainder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.PadicRemainder.paper1_padic_log_quadratic_remainder_bound_false
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
