import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourSignedDominance

/-! A quantitative elementary bound for the literal all-residue q¹ tail. -/

namespace ManuscriptAudit.Paper8ContourAllResidueTail

open MeasureTheory Set
open Paper8ContourSignedDominance (decay decay_nonneg decay_tail_summable)

noncomputable section

theorem decay_eq_rpow {k : ℕ} (hk : 0 < k) : decay k = (k : ℝ) ^ (-(5 / 2) : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold decay
  rw [Real.rpow_neg hkR.le, show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
    Real.rpow_add hkR, Real.rpow_two, ← Real.sqrt_eq_rpow, one_div]

private theorem decay_le_of_square_bound (k : ℕ) (hk : 0 < k) (v : ℝ) (hv : 0 < v)
    (hs : v ^ 2 ≤ (k : ℝ)) : decay k ≤ 1 / ((k : ℝ) ^ 2 * v) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold decay
  exact one_div_le_one_div_of_le (mul_pos (pow_pos hkR _) hv)
    (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hs) (sq_nonneg _))

private theorem last_tail_le :
    (∑' n : ℕ, decay (n + 9)) ≤ 5 / 168 := by
  have hSub : Ici (8 : ℝ) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le (by norm_num) (Set.mem_Ici.mp hx))
  have hAnti : AntitoneOn (fun x : ℝ => x ^ (-(5 / 2) : ℝ)) (Ici (8 : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num : (-(5 / 2) : ℝ) ≤ 0)).mono hSub
  have hInt := hAnti.tsum_comp_add_le_integral 8
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(5 / 2) : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 8))
    (fun x hx => Real.rpow_nonneg ((by norm_num : (0 : ℝ) ≤ 8).trans (Set.mem_Ioi.mp hx).le) _)
  have hFun : (fun n : ℕ => ((n + 8 + 1 : ℕ) : ℝ) ^ (-(5 / 2) : ℝ)) =
      (fun n : ℕ => decay (n + 9)) := by
    funext n
    exact (decay_eq_rpow (by omega : 0 < n + 9)).symm
  have hTarget : (∑' n : ℕ, decay (n + 9)) ≤
      ∫ x in Ioi (8 : ℝ), x ^ (-(5 / 2) : ℝ) := by
    rw [← hFun]
    exact hInt
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(5 / 2) : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 8)] at hTarget
  have hEight : (8 : ℝ) ^ ((-(5 / 2) : ℝ) + 1) = 1 / (8 * Real.sqrt 8) := by
    rw [show (-(5 / 2) : ℝ) + 1 = -(1 + 1 / 2) by norm_num,
      Real.rpow_neg (by norm_num : 0 ≤ (8 : ℝ)), Real.rpow_add (by norm_num : 0 < (8 : ℝ)),
      Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
  rw [hEight] at hTarget
  have hSqrt : (14 / 5 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
  calc
    _ ≤ (2 / 3 : ℝ) / (8 * Real.sqrt 8) := by
      convert hTarget using 1 <;> ring
    _ ≤ (2 / 3 : ℝ) / (8 * (14 / 5)) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (mul_le_mul_of_nonneg_left hSqrt (by norm_num))
    _ = _ := by norm_num

private theorem first_six_le :
    (∑ n ∈ Finset.range 6, decay (n + 3)) ≤
      10 / 153 + 1 / 32 + 1 / 55 + 5 / 432 + 5 / 637 + 5 / 896 := by
  have d3 := decay_le_of_square_bound 3 (by decide) (17 / 10) (by norm_num) (by norm_num)
  have d4 := decay_le_of_square_bound 4 (by decide) 2 (by norm_num) (by norm_num)
  have d5 := decay_le_of_square_bound 5 (by decide) (11 / 5) (by norm_num) (by norm_num)
  have d6 := decay_le_of_square_bound 6 (by decide) (12 / 5) (by norm_num) (by norm_num)
  have d7 := decay_le_of_square_bound 7 (by decide) (13 / 5) (by norm_num) (by norm_num)
  have d8 := decay_le_of_square_bound 8 (by decide) (14 / 5) (by norm_num) (by norm_num)
  norm_num at d3 d4 d5 d6 d7 d8
  norm_num [Finset.sum_range_succ] <;> linarith

theorem scaled_tail_three_lt :
    (8 * Real.sqrt 2) * (∑' n : ℕ, decay (n + 3)) < 48 / 25 := by
  let B : ℝ := 10 / 153 + 1 / 32 + 1 / 55 + 5 / 432 + 5 / 637 + 5 / 896 + 5 / 168
  have hSplit : (∑ n ∈ Finset.range 6, decay (n + 3)) + (∑' n : ℕ, decay (n + 9)) =
      ∑' n : ℕ, decay (n + 3) := by
    simpa only [Nat.add_assoc] using (decay_tail_summable 3 (by decide)).sum_add_tsum_nat_add 6
  have hB : (∑' n : ℕ, decay (n + 3)) ≤ B := by
    rw [← hSplit]
    exact add_le_add first_six_le last_tail_le
  have hSqrt : Real.sqrt 2 ≤ (99 / 70 : ℝ) := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hPos : 0 ≤ ∑' n : ℕ, decay (n + 3) := tsum_nonneg (fun _ => decay_nonneg _)
  calc
    _ ≤ (8 * (99 / 70 : ℝ)) * B :=
      mul_le_mul (mul_le_mul_of_nonneg_left hSqrt (by norm_num)) hB hPos (by norm_num)
    _ < _ := by norm_num [B]

theorem cosine_lower_bound : (48 / 25 : ℝ) < 1 + Real.cos (Real.pi / 8) := by
  have hArg : Real.pi / 8 < (2 / 5 : ℝ) := by linarith [Real.pi_lt_d2]
  have hProd : 0 < ((2 / 5 : ℝ) - Real.pi / 8) * ((2 / 5 : ℝ) + Real.pi / 8) :=
    mul_pos (sub_pos.mpr hArg) (by positivity)
  nlinarith only [hProd, Real.one_sub_sq_div_two_le_cos (x := Real.pi / 8)]

end
end ManuscriptAudit.Paper8ContourAllResidueTail

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourAllResidueTail.decay_eq_rpow,
      ``ManuscriptAudit.Paper8ContourAllResidueTail.scaled_tail_three_lt,
      ``ManuscriptAudit.Paper8ContourAllResidueTail.cosine_lower_bound] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
