import Lean.Util.CollectAxioms
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdOrderedLimit

/-!
# The odd-gcd transfer scalar is strictly positive

The scale on positive odd indices is the signed p-series at
exponent 3/2. Pairing indices 4j+1 and 4j+3 proves strict positivity
and hence preserves whether the transported reduced mode is zero.
-/

namespace ManuscriptAudit.Paper8OddGcdScalar

open Paper8OddGcdResiduePhase (oddFactorSign)
open Paper8OddGcdOrderedLimit (oddScale oddScale_norm_summable)

noncomputable section

private theorem odd_scale_re_odd_index (m : ℕ) :
    (oddScale (2 * m + 1)).re = (-1 : ℝ)^m * (1 / ((2 * m + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) := by
  have hOdd : Odd (2 * m + 1) := ⟨m, by omega⟩
  have hExp : (2 * m + 1 - 1) / 2 = m := by omega
  have hCast : (((-1 : ℝ)^m : ℝ) : ℂ) = (-1 : ℂ)^m := by push_cast; rfl
  rw [oddScale, if_pos hOdd, oddFactorSign, hExp, ← hCast, ← Complex.ofReal_mul,
    Complex.ofReal_re]

set_option maxHeartbeats 800000 in
theorem odd_scale_tsum_re_pos : 0 < (∑' j : ℕ, oddScale (j + 1)).re := by
  let f (j : ℕ) : ℝ := (oddScale (j + 1)).re
  rw [Complex.re_tsum oddScale_norm_summable.of_norm]
  change 0 < ∑' j : ℕ, f j
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ oddScale_norm_summable
    intro j
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (oddScale (j + 1))
  have hDouble : Function.Injective (fun m : ℕ => 2 * m) :=
    mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0)
  have hDoubleSucc : Function.Injective (fun m : ℕ => 2 * m + 1) :=
    (add_left_injective 1).comp hDouble
  have he : Summable (fun m : ℕ => f (2 * m)) := hf.comp_injective hDouble
  have ho : Summable (fun m : ℕ => f (2 * m + 1)) := hf.comp_injective hDoubleSucc
  have hZero (m : ℕ) : f (2 * m + 1) = 0 := by
    have hEven : Even (2 * m + 1 + 1) := ⟨m + 1, by omega⟩
    change (oddScale (2 * m + 1 + 1)).re = 0
    rw [oddScale, if_neg (Nat.not_odd_iff_even.mpr hEven)]
    rfl
  have hee : Summable (fun m : ℕ => f (2 * (2 * m))) := he.comp_injective hDouble
  have heo : Summable (fun m : ℕ => f (2 * (2 * m + 1))) := he.comp_injective hDoubleSucc
  let a (m : ℕ) : ℝ := 1 / ((4 * m + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)
  let b (m : ℕ) : ℝ := 1 / ((4 * m + 3 : ℕ) : ℝ) ^ (3 / 2 : ℝ)
  have hA (m : ℕ) : f (2 * (2 * m)) = a m := by
    change (oddScale (2 * (2 * m) + 1)).re = _
    have hEven : Even (2 * m) := ⟨m, by omega⟩
    rw [odd_scale_re_odd_index, hEven.neg_one_pow, one_mul]
    change 1 / ((2 * (2 * m) + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
      1 / ((4 * m + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)
    rw [show 2 * (2 * m) + 1 = 4 * m + 1 by omega]
  have hB (m : ℕ) : f (2 * (2 * m + 1)) = -b m := by
    change (oddScale (2 * (2 * m + 1) + 1)).re = _
    have hOdd : Odd (2 * m + 1) := ⟨m, by omega⟩
    rw [odd_scale_re_odd_index, hOdd.neg_one_pow, neg_one_mul]
    change -(1 / ((2 * (2 * m + 1) + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) =
      -(1 / ((4 * m + 3 : ℕ) : ℝ) ^ (3 / 2 : ℝ))
    rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 by omega]
  have ha : Summable a := hee.congr hA
  have hb : Summable b := heo.neg.congr fun m => by simp only [hB, neg_neg]
  have hStrict (m : ℕ) : b m < a m := by
    have hx : 0 < ((4 * m + 1 : ℕ) : ℝ) := by positivity
    have hxy : ((4 * m + 1 : ℕ) : ℝ) < ((4 * m + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 4 * m + 1 < 4 * m + 3 by omega)
    exact one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos hx _)
      (Real.rpow_lt_rpow hx.le hxy (by norm_num : (0 : ℝ) < 3 / 2))
  rw [← tsum_even_add_odd he ho, ← tsum_even_add_odd hee heo]
  simp only [hZero, hA, hB, tsum_zero, add_zero, tsum_neg, ← sub_eq_add_neg]
  rw [← ha.tsum_sub hb, (ha.sub hb).tsum_eq_zero_add]
  exact add_pos_of_pos_of_nonneg (sub_pos.mpr (hStrict 0))
    (tsum_nonneg fun m => sub_nonneg.mpr (hStrict (m + 1)).le)

theorem odd_scale_tsum_ne_zero : (∑' j : ℕ, oddScale (j + 1)) ≠ 0 := by
  intro h
  have hp := odd_scale_tsum_re_pos
  rw [h, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem odd_transferred_limit_eq_zero_iff (L : ℂ) :
    (∑' j : ℕ, oddScale (j + 1) * L) = 0 ↔ L = 0 := by
  rw [tsum_mul_right, mul_eq_zero]
  simp only [odd_scale_tsum_ne_zero, false_or]

end
end ManuscriptAudit.Paper8OddGcdScalar

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddGcdScalar.odd_scale_tsum_re_pos,
      ``ManuscriptAudit.Paper8OddGcdScalar.odd_transferred_limit_eq_zero_iff] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
