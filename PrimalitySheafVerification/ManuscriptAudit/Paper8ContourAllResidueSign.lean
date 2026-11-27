import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourAllResidueTail
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourSignedCoefficient

/-! The signed q¹ difference for the literal all-residue reading has negative real part. -/

namespace ManuscriptAudit.Paper8ContourAllResidueSign

open Paper8ContourAllResidueTail (decay_eq_rpow scaled_tail_three_lt cosine_lower_bound)
open Paper8ContourSignedDominance (decay decay_tail_summable)
open Paper8ContourCoefficientDecay (delta delta_eq_moments delta_nonneg delta_le_scaled)
open Paper8ContourMoment (atZero_literal_lt_rhoades)
open Paper8ContourResidueWeights (allWeight weighted_norm_le_two)
open Paper8ContourSignedCoefficient (all_difference_summable all_first_term_zero all_second_term_re)

noncomputable section

private theorem delta_two_pos : 0 < delta 2 := by
  rw [delta_eq_moments (by decide : 0 < (2 : ℕ)) (r := 1) zero_lt_one]
  exact sub_pos.mpr (atZero_literal_lt_rhoades (by decide : 0 < (2 : ℕ)) zero_lt_one)

private theorem delta_le_scaled_two {k : ℕ} (hk : 2 ≤ k) :
    delta k ≤ ((4 * Real.sqrt 2) * decay k) * delta 2 := by
  have hK : 0 < k := by omega
  have hKR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hTwo : (2 : ℝ) ^ (5 / 2 : ℝ) = 4 * Real.sqrt 2 := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_two, ← Real.sqrt_eq_rpow]
    norm_num
  have hDecay : ((k : ℝ) ^ (5 / 2 : ℝ))⁻¹ = decay k := by
    rw [decay_eq_rpow hK, Real.rpow_neg hKR]
  have h := delta_le_scaled (by decide : 0 < (2 : ℕ)) hk
  rw [Nat.cast_two, Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hKR,
    hTwo, div_eq_mul_inv, hDecay] at h
  exact h

private theorem all_tail_norm_lt :
    ‖∑' n : ℕ, allWeight (n + 3) * (delta (n + 3) : ℂ)‖ < (48 / 25 : ℝ) * delta 2 := by
  let C : ℝ := (8 * Real.sqrt 2) * delta 2
  have hMajorant : Summable (fun n : ℕ => C * decay (n + 3)) :=
    (decay_tail_summable 3 (by decide)).mul_left C
  have hNorm (n : ℕ) : ‖allWeight (n + 3) * (delta (n + 3) : ℂ)‖ ≤ C * decay (n + 3) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (delta_nonneg _)]
    calc
      _ ≤ 2 * (((4 * Real.sqrt 2) * decay (n + 3)) * delta 2) :=
        mul_le_mul (weighted_norm_le_two (by omega : 0 < n + 3) Finset.univ)
          (delta_le_scaled_two (by omega)) (delta_nonneg _) (by norm_num)
      _ = _ := by unfold C; ring
  have hAbs : Summable (fun n => ‖allWeight (n + 3) * (delta (n + 3) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hNorm hMajorant
  calc
    _ ≤ ∑' n : ℕ, ‖allWeight (n + 3) * (delta (n + 3) : ℂ)‖ := norm_tsum_le_tsum_norm hAbs
    _ ≤ ∑' n : ℕ, C * decay (n + 3) := hAbs.tsum_le_tsum hNorm hMajorant
    _ = C * (∑' n : ℕ, decay (n + 3)) := tsum_mul_left
    _ = ((8 * Real.sqrt 2) * (∑' n : ℕ, decay (n + 3))) * delta 2 := by unfold C; ring
    _ < _ := mul_lt_mul_of_pos_right scaled_tail_three_lt delta_two_pos

theorem all_difference_real_negative :
    (∑' n : ℕ, allWeight (n + 1) * (delta (n + 1) : ℂ)).re < 0 := by
  let T : ℕ → ℂ := fun n => allWeight (n + 1) * (delta (n + 1) : ℂ)
  have hT : Summable T := all_difference_summable
  have hTail : Summable (fun n => T (n + 1)) := (summable_nat_add_iff 1).2 hT
  have hSplit : (∑' n : ℕ, T n) = T 0 + (T 1 + ∑' n : ℕ, T (n + 2)) := by
    rw [hT.tsum_eq_zero_add, hTail.tsum_eq_zero_add]
  have hFirst : T 0 = 0 := all_first_term_zero
  have hSecond : (T 1).re = -(1 + Real.cos (Real.pi / 8)) * delta 2 := all_second_term_re
  have hTailNorm : ‖∑' n : ℕ, T (n + 2)‖ < (48 / 25 : ℝ) * delta 2 := all_tail_norm_lt
  have hRe : (∑' n : ℕ, T (n + 2)).re ≤ ‖∑' n : ℕ, T (n + 2)‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  change (∑' n : ℕ, T n).re < 0
  rw [hSplit, hFirst, zero_add, Complex.add_re, hSecond]
  have hCos := mul_lt_mul_of_pos_right cosine_lower_bound delta_two_pos
  nlinarith only [hCos, hTailNorm, hRe]

end
end ManuscriptAudit.Paper8ContourAllResidueSign

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8ContourAllResidueSign.all_difference_real_negative
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms name
  let bad := axioms.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {axioms}"
