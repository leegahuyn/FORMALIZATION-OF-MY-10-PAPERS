import Lean.Util.CollectAxioms
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenDenominatorSignTable
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenDenominatorWeights

/-! The four exact limits of the signed even denominator weights. -/

namespace ManuscriptAudit.Paper8EvenDenominatorWeightLimits

open Paper8EvenDenominatorSignTable
open Paper8EvenGcdOrderedLimit (evenWeight evenWeight_norm_summable)
open Paper8OddGcdOrderedLimit (oddScale oddScale_norm_summable)

noncomputable section

def inversePower (h : ℕ) : ℂ := ((1 / (h : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ)

def zetaWeight : ℂ := ∑' j : ℕ, inversePower (j + 1)

def alternatingWeight : ℂ := ∑' j : ℕ, (-1 : ℂ) ^ (j + 1) * inversePower (j + 1)

def betaWeight : ℂ := ∑' j : ℕ, oddScale (j + 1)

def evenWeightLimit (D : ℕ) : ℂ := ∑' j : ℕ, evenWeight (j + 1) D

private theorem inversePower_mul {h D : ℕ} (hh : 0 < h) (hD : 0 < D) :
    inversePower (h * D) = inversePower h * inversePower D := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  unfold inversePower
  rw [Nat.cast_mul, Real.mul_rpow hhR.le hDR.le, ← Complex.ofReal_mul]
  congr 1
  field_simp [(Real.rpow_pos_of_pos hhR (3 / 2 : ℝ)).ne',
    (Real.rpow_pos_of_pos hDR (3 / 2 : ℝ)).ne'] <;> ring

private theorem double_injective : Function.Injective (fun m : ℕ => 2 * m) :=
  mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0)

private theorem double_succ_injective : Function.Injective (fun m : ℕ => 2 * m + 1) :=
  (add_left_injective 1).comp double_injective

private theorem beta_on_positive_odd :
    (∑' j : ℕ, oddScale (2 * j + 1)) = betaWeight := by
  have hAll : Summable (fun j : ℕ => oddScale (j + 1)) := oddScale_norm_summable.of_norm
  have hEven : Summable (fun j : ℕ => oddScale (2 * j + 1)) := hAll.comp_injective double_injective
  have hOdd : Summable (fun j : ℕ => oddScale (2 * j + 1 + 1)) := hAll.comp_injective double_succ_injective
  have hZero : (∑' j : ℕ, oddScale (2 * j + 1 + 1)) = 0 := by
    calc
      _ = ∑' _ : ℕ, (0 : ℂ) := by
        refine tsum_congr fun j => ?_
        have he : Even (2 * j + 1 + 1) := ⟨j + 1, by omega⟩
        rw [oddScale, if_neg (Nat.not_odd_iff_even.mpr he)]
      _ = _ := tsum_zero
  unfold betaWeight
  rw [← tsum_even_add_odd hEven hOdd, hZero, add_zero]

theorem even_weight_limit_zero_class {D : ℕ} (hD : D % 4 = 0) :
    evenWeightLimit D = alternatingWeight := by
  unfold evenWeightLimit alternatingWeight
  refine tsum_congr fun j => ?_
  change inversePower (j + 1) * _ = _
  rw [sign_zero_class hD, mul_comm]

theorem even_weight_limit_two_class {D : ℕ} (hD : D % 4 = 2) :
    evenWeightLimit D = zetaWeight := by
  unfold evenWeightLimit zetaWeight
  refine tsum_congr fun j => ?_
  change inversePower (j + 1) * _ = _
  rw [sign_two_class hD, mul_one]

private theorem positive_even_indices_sum {D : ℕ} (hD : Odd D) :
    (∑' j : ℕ, evenWeight (2 * j + 1 + 1) D) = inversePower 2 * alternatingWeight := by
  unfold alternatingWeight
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega]
  change inversePower (2 * (j + 1)) * _ = _
  rw [inversePower_mul (by decide : 0 < (2 : ℕ)) (Nat.succ_pos j),
    sign_even_index_of_odd_denominator hD]
  ring

private theorem odd_denominator_split (D : ℕ) :
    evenWeightLimit D =
      (∑' j : ℕ, evenWeight (2 * j + 1) D) + ∑' j : ℕ, evenWeight (2 * j + 1 + 1) D := by
  have hs : Summable (fun j : ℕ => evenWeight (j + 1) D) := (evenWeight_norm_summable D).of_norm
  have he : Summable (fun j : ℕ => evenWeight (2 * j + 1) D) := hs.comp_injective double_injective
  have ho : Summable (fun j : ℕ => evenWeight (2 * j + 1 + 1) D) := hs.comp_injective double_succ_injective
  exact (tsum_even_add_odd he ho).symm

theorem even_weight_limit_one_class {D : ℕ} (hD : D % 4 = 1) :
    evenWeightLimit D = inversePower 2 * alternatingWeight - betaWeight := by
  have hOdd : Odd D := ⟨D / 2, by omega⟩
  have h : (∑' j : ℕ, evenWeight (2 * j + 1) D) = -betaWeight := by
    rw [← beta_on_positive_odd, ← tsum_neg]
    refine tsum_congr fun j => ?_
    have hj : Odd (2 * j + 1) := ⟨j, by omega⟩
    rw [evenWeight, oddScale, if_pos hj, sign_odd_index_of_one_class hj hD]
    ring
  rw [odd_denominator_split, h, positive_even_indices_sum hOdd]
  ring

theorem even_weight_limit_three_class {D : ℕ} (hD : D % 4 = 3) :
    evenWeightLimit D = inversePower 2 * alternatingWeight + betaWeight := by
  have hOdd : Odd D := ⟨D / 2, by omega⟩
  have h : (∑' j : ℕ, evenWeight (2 * j + 1) D) = betaWeight := by
    rw [← beta_on_positive_odd]
    refine tsum_congr fun j => ?_
    have hj : Odd (2 * j + 1) := ⟨j, by omega⟩
    rw [evenWeight, oddScale, if_pos hj, sign_odd_index_of_three_class hj hD]
    ring
  rw [odd_denominator_split, h, positive_even_indices_sum hOdd, add_comm betaWeight]

end
end ManuscriptAudit.Paper8EvenDenominatorWeightLimits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenDenominatorWeightLimits.even_weight_limit_zero_class,
      ``ManuscriptAudit.Paper8EvenDenominatorWeightLimits.even_weight_limit_two_class,
      ``ManuscriptAudit.Paper8EvenDenominatorWeightLimits.even_weight_limit_one_class,
      ``ManuscriptAudit.Paper8EvenDenominatorWeightLimits.even_weight_limit_three_class] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
