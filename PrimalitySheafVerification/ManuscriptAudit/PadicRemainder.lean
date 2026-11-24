import Mathlib.Data.Nat.Prime.Nth
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

private theorem logarithm_remainder_of_denominator_bound {p : ℕ} [Fact p.Prime]
    (e k : ℕ) (hk : 1 ≤ k) {x : ℚ_[p]}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ)))
    (hVal : ∀ i : ℕ, padicValNat p (i + 2) ≤ i + e) :
    ‖padicLog1p x - x‖ ≤ (p : ℝ) ^ ((e : ℤ) - 2 * (k : ℤ)) := by
  have hpRlt : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpRpos : (0 : ℝ) < (p : ℝ) := zero_lt_one.trans hpRlt
  have hRadiusPow : (p : ℝ) ^ (-(k : ℤ)) < 1 := by
    rw [zpow_neg, zpow_natCast, inv_lt_one₀ (pow_pos hpRpos k)]
    exact one_lt_pow₀ hpRlt (by omega)
  have hRadius : ‖x‖ < 1 := hx.trans_lt hRadiusPow
  have hSummable := padicLogSeries_summable hRadius
  have hSplit := Summable.sum_add_tsum_nat_add 2 hSummable
  have hPrefix : (∑ n ∈ Finset.range 2, padicLogSeries x n) = x :=
    padicLogTrunc_two x
  rw [hPrefix] at hSplit
  change x + (∑' i : ℕ, padicLogSeries x (i + 2)) = padicLog1p x at hSplit
  have hTail : padicLog1p x - x = ∑' i : ℕ, padicLogSeries x (i + 2) := by
    rw [← hSplit]
    abel
  rw [hTail]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro i
  have hi : (i + 2 : ℕ) ≠ 0 := by omega
  have hcast : ((i + 2 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hi
  have hDenNorm :
      ‖((i + 2 : ℕ) : ℚ_[p])‖⁻¹ = (p : ℝ) ^ padicValNat p (i + 2) := by
    rw [Padic.norm_eq_zpow_neg_valuation hcast, Padic.valuation_natCast,
      zpow_neg, inv_inv, zpow_natCast]
  calc
    ‖padicLogSeries x (i + 2)‖ =
        ‖x‖ ^ (i + 2) * ‖((i + 2 : ℕ) : ℚ_[p])‖⁻¹ := by
      simp only [padicLogSeries, div_eq_mul_inv, norm_mul, norm_pow, norm_neg,
        norm_one, one_pow, one_mul, norm_inv]
    _ = ‖x‖ ^ (i + 2) * (p : ℝ) ^ padicValNat p (i + 2) := by rw [hDenNorm]
    _ ≤ ((p : ℝ) ^ (-(k : ℤ))) ^ (i + 2) * (p : ℝ) ^ padicValNat p (i + 2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx (i + 2))
        (pow_nonneg hpRpos.le _)
    _ =
        (p : ℝ) ^ (-(k : ℤ) * ((i + 2 : ℕ) : ℤ) +
          (padicValNat p (i + 2) : ℤ)) := by
      rw [← zpow_natCast ((p : ℝ) ^ (-(k : ℤ))) (i + 2),
        ← zpow_mul, ← zpow_natCast (p : ℝ) (padicValNat p (i + 2)),
        ← zpow_add₀ hpRpos.ne']
    _ ≤ (p : ℝ) ^ ((e : ℤ) - 2 * (k : ℤ)) := by
      apply zpow_le_zpow_right₀ hpRlt.le
      have hValInt : (padicValNat p (i + 2) : ℤ) ≤ (i : ℤ) + (e : ℤ) := by
        exact_mod_cast hVal i
      have hkInt : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      have hiInt : (0 : ℤ) ≤ (i : ℤ) := by positivity
      have hMul : (i : ℤ) ≤ (k : ℤ) * (i : ℤ) := by
        calc
          (i : ℤ) = 1 * (i : ℤ) := (one_mul _).symm
          _ ≤ (k : ℤ) * (i : ℤ) := mul_le_mul_of_nonneg_right hkInt hiInt
      have hBound : (padicValNat p (i + 2) : ℤ) ≤ (k : ℤ) * (i : ℤ) + (e : ℤ) := by
        linarith only [hValInt, hMul]
      have hRewrite :
          -(k : ℤ) * ((i + 2 : ℕ) : ℤ) + (padicValNat p (i + 2) : ℤ) =
            -(2 * (k : ℤ)) + ((padicValNat p (i + 2) : ℤ) - (k : ℤ) * (i : ℤ)) := by
        push_cast
        ring
      rw [hRewrite]
      linarith only [hBound]

/-- Paper 1, p. 10, Lemma 2.3. For an odd prime, the actual logarithm
remainder on the p⁻ᵏ ball has norm at most p⁻²ᵏ. -/
theorem paper1_odd_prime_log_quadratic_remainder {p : ℕ} [Fact (Nat.Prime p)]
    (hp : 3 ≤ p) (k : ℕ) (hk : 1 ≤ k) {x : ℚ_[p]}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ))) :
    ‖padicLog1p x - x‖ ≤ (p : ℝ) ^ (-(2 * (k : ℤ))) := by
  have hpPos : 0 < p := by omega
  have hGrowth (i : ℕ) : i + 2 < p ^ (i + 1) := by
    induction i with
    | zero =>
      simpa only [Nat.zero_add, pow_one] using (show 2 < p by omega)
    | succ i ih =>
      calc
        i.succ + 2 = i + 3 := by omega
        _ < (i + 2) * 2 := by omega
        _ ≤ p ^ (i + 1) * p := Nat.mul_le_mul ih.le (by omega)
        _ = p ^ (i.succ + 1) := by rw [← pow_succ] <;> rfl
  have hVal (i : ℕ) : padicValNat p (i + 2) ≤ i := by
    by_contra h
    have hIndices : i + 1 ≤ padicValNat p (i + 2) := by omega
    have hDvd : p ^ padicValNat p (i + 2) ∣ i + 2 := pow_padicValNat_dvd
    exact (not_lt_of_ge ((Nat.pow_le_pow_right hpPos hIndices).trans
      (Nat.le_of_dvd (by omega) hDvd))) (hGrowth i)
  simpa only [Nat.cast_zero, zero_sub] using
    logarithm_remainder_of_denominator_bound 0 k hk hx (by simpa using hVal)

/-- Corrected uniform bound including the prime two. The two-adic
counterexample above attains the loss of one valuation digit. -/
theorem paper1_uniform_log_quadratic_remainder_with_loss {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : 1 ≤ k) {x : ℚ_[p]}
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ))) :
    ‖padicLog1p x - x‖ ≤ (p : ℝ) ^ (1 - 2 * (k : ℤ)) := by
  have hVal (i : ℕ) : padicValNat p (i + 2) ≤ i + 1 := by
    have hLt := (padicValNat_le_nat_log (p := p) (i + 2)).trans_lt
      (Nat.log_lt_self p (by omega : (i + 2 : ℕ) ≠ 0))
    omega
  simpa only [Nat.cast_one] using logarithm_remainder_of_denominator_bound 1 k hk hx hVal

/-- Paper 1, p. 7, Remark 2.2. With p=2, n=k=2, A=9, m=1
and y=4 on the minus branch, the printed expansion uses p₂=3 and its
per-term hypothesis holds.
The actual logarithm remainder at the resulting discrepancy exceeds 2⁻⁴. -/
theorem paper1_printed_parameters_violate_unrestricted_remainder :
    Nat.nth Nat.Prime 1 = 3 ∧ (3 * 4 - (9 - 1) : ℤ) = 4 ∧
      Spt1.Hk 2 4 9 1 2 2 ((9 : ℤ) ^ 3) ∧
      (9 : ℚ) ^ 3 =
        (81 : ℚ) * (Spt1.Snexp 9 2 : ℚ) +
          Spt1.canonExpTail 4 9 1 (fun j => if j = 0 then -729 else 0) 2 ∧
      (1 : ℝ) / 16 <
        ‖padicLog1p (((3645 : ℚ_[2]) - 729) / 729) -
          (((3645 : ℚ_[2]) - 729) / 729)‖ := by
  have hDen : padicValNat 2 729 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by decide)
  have hFour : padicValNat 2 4 = 2 := by
    change padicValNat 2 (2 ^ 2) = 2
    rw [padicValNat.pow, padicValNat_self] <;> norm_num
  have hForty : padicValNat 2 40 = 3 := by
    change padicValNat 2 ((2 ^ 3) * 5) = 3
    rw [padicValNat.mul (by decide) (by decide), padicValNat.pow, padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 5)] <;> norm_num
  have hY : (9 : ℤ) ^ 3 = 729 := by norm_num
  refine ⟨Nat.nth_prime_one_eq_three, by norm_num, ?_, ?_, ?_⟩
  · rw [hY]
    intro j hj
    have hCases : j = 0 ∨ j = 1 := by omega
    rcases hCases with rfl | rfl
    · have hPhi : Spt1.phiTerm 4 9 1 729 0 =
          ((4 : ℕ) : ℚ) / ((729 : ℕ) : ℚ) := by
        norm_num [Spt1.phiTerm, Spt1.Sbinom]
      rw [hPhi, padicValRat.div (by norm_num) (by norm_num),
        padicValRat.of_nat, padicValRat.of_nat, hFour, hDen]
      norm_num
    · have hPhi : Spt1.phiTerm 4 9 1 729 1 =
          ((40 : ℕ) : ℚ) / ((729 : ℕ) : ℚ) := by
        norm_num [Spt1.phiTerm, Spt1.Sbinom]
      rw [hPhi, padicValRat.div (by norm_num) (by norm_num),
        padicValRat.of_nat, padicValRat.of_nat, hForty, hDen]
      norm_num
  · norm_num [Spt1.Snexp, Spt1.Sbinom, Spt1.canonExpTail,
      Finset.sum_range_succ, show (10 : ℕ).choose 2 = 45 by decide]
  · rw [show ((3645 : ℚ_[2]) - 729) / 729 = 4 by norm_num,
      norm_padic_log_remainder_four]
    norm_num

end ManuscriptAudit.PadicRemainder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PadicRemainder.paper1_padic_log_quadratic_remainder_bound_false,
      ``ManuscriptAudit.PadicRemainder.paper1_odd_prime_log_quadratic_remainder,
      ``ManuscriptAudit.PadicRemainder.paper1_uniform_log_quadratic_remainder_with_loss,
      ``ManuscriptAudit.PadicRemainder.paper1_printed_parameters_violate_unrestricted_remainder] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
