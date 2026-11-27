import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplex
import PrimalitySheafVerification.ManuscriptAudit.Paper8InsideComplexComparison

/-!
# A radial obstruction at the negative unit boundary for the p. 314 series

Odd terms followed by even terms form nonpositive pairs on the negative
real radius. The first pair forces the actual exterior series below a
quantity diverging to negative infinity at the boundary `q=-1`.
-/

namespace ManuscriptAudit.Paper8ExteriorNegativeRadius

open Paper8ExteriorNormalization (negPochhammer)
open Paper8InsideComplexComparison Paper8ExteriorComplex

noncomputable section

private def realTerm (r : ℝ) (n : ℕ) : ℝ :=
  (-r) ^ n / negPochhammer (-r) n ^ 2

private def pair (r : ℝ) (k : ℕ) : ℝ :=
  realTerm r (2 * k + 1) + realTerm r (2 * k + 2)

private theorem realTerm_cast (r : ℝ) (n : ℕ) :
    ((realTerm r n : ℝ) : ℂ) = exteriorTerm n ((-r : ℝ) : ℂ) := by
  rw [realTerm, exteriorTerm, pochhammer_ofReal, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_pow]

private theorem realTerm_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (realTerm r) := by
  have hNorm : ‖((-r : ℝ) : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr] using h₁
  apply Complex.summable_ofReal.mp
  simpa only [realTerm_cast] using (exterior_absolute_summability hNorm).of_norm

private theorem realTerm_succ (r : ℝ) (n : ℕ) :
    realTerm r (n + 1) = realTerm r n * ((-r) / (1 + (-r) ^ (n + 1)) ^ 2) := by
  have hPoch : negPochhammer (-r) (n + 1) =
      negPochhammer (-r) n * (1 + (-r) ^ (n + 1)) := by
    simp only [negPochhammer, Finset.prod_range_succ]
  unfold realTerm
  rw [hPoch, mul_pow, pow_succ (-r) n, div_mul_div_comm]

private theorem realTerm_odd_nonpos (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    realTerm r (2 * k + 1) ≤ 0 := by
  unfold realTerm
  rw [pow_succ, pow_mul, neg_sq]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (sq_nonneg r) k) (neg_nonpos.mpr hr))
    (sq_nonneg _)

private theorem pair_factor (r : ℝ) (k : ℕ) :
    pair r k = realTerm r (2 * k + 1) * (1 - r / (1 + r ^ (2 * k + 2)) ^ 2) := by
  have hPow : (-r) ^ (2 * k + 2) = r ^ (2 * k + 2) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul, pow_mul, neg_sq]
  have hNext := realTerm_succ r (2 * k + 1)
  change realTerm r (2 * k + 2) =
      realTerm r (2 * k + 1) * ((-r) / (1 + (-r) ^ (2 * k + 2)) ^ 2) at hNext
  rw [pair, hNext, hPow, neg_div]
  ring

private theorem pair_nonpos (r : ℝ) (hr : 0 ≤ r) (h₁ : r < 1) (k : ℕ) :
    pair r k ≤ 0 := by
  rw [pair_factor]
  refine mul_nonpos_of_nonpos_of_nonneg (realTerm_odd_nonpos r hr k) (sub_nonneg.mpr ?_)
  have hDen : 1 ≤ (1 + r ^ (2 * k + 2)) ^ 2 := by
    nlinarith only [pow_nonneg hr (2 * k + 2), sq_nonneg (r ^ (2 * k + 2))]
  exact (div_le_one (zero_lt_one.trans_le hDen)).mpr (h₁.le.trans hDen)

private theorem pair_zero_le (r : ℝ) (hr : 0 ≤ r) (h₁ : r < 1) :
    pair r 0 ≤ -(r / (2 * (1 - r) ^ 2)) := by
  have hDen : 2 * r ≤ (1 + r ^ 2) ^ 2 := by
    nlinarith only [sq_nonneg (r - 1), sq_nonneg r, sq_nonneg (r ^ 2)]
  have hRatio : r / (1 + r ^ 2) ^ 2 ≤ 1 / 2 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith only [hDen])
  have hWeight : (1 / 2 : ℝ) ≤ 1 - r / (1 + r ^ 2) ^ 2 := by linarith only [hRatio]
  have hPair := pair_factor r 0
  change pair r 0 = realTerm r 1 * (1 - r / (1 + r ^ 2) ^ 2) at hPair
  rw [hPair]
  calc
    _ ≤ realTerm r 1 * (1 / 2) :=
      mul_le_mul_of_nonpos_left hWeight (realTerm_odd_nonpos r hr 0)
    _ = _ := by
      have hTerm : realTerm r 1 = -r / (1 - r) ^ 2 := by
        simp [realTerm, negPochhammer, sub_eq_add_neg]
      rw [hTerm]
      field_simp [sub_ne_zero.mpr (ne_of_gt h₁)] <;> ring

theorem negative_radial_upper {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    (exterior (-(r : ℂ))).re ≤ 1 - r / (2 * (1 - r) ^ 2) := by
  have hSumm := realTerm_summable hr h₁
  have hCast := Complex.ofRealCLM.hasSum hSumm.hasSum
  change HasSum (fun n => ((realTerm r n : ℝ) : ℂ)) ((∑' n, realTerm r n : ℝ) : ℂ) at hCast
  simp only [realTerm_cast, Complex.ofReal_neg] at hCast
  have hEq : exterior (-(r : ℂ)) = ((∑' n, realTerm r n : ℝ) : ℂ) := hCast.tsum_eq
  rw [hEq, Complex.ofReal_re]
  have hTail : Summable (fun n : ℕ => realTerm r (n + 1)) := (summable_nat_add_iff 1).mpr hSumm
  have hEven : Summable (fun k : ℕ => realTerm r (2 * k + 1)) := by
    change Summable ((fun n : ℕ => realTerm r (n + 1)) ∘ fun k : ℕ => 2 * k)
    exact hTail.comp_injective (fun _ _ h => by omega)
  have hOdd : Summable (fun k : ℕ => realTerm r (2 * k + 2)) := by
    change Summable ((fun n : ℕ => realTerm r (n + 1)) ∘ fun k : ℕ => 2 * k + 1)
    exact hTail.comp_injective (fun _ _ h => by omega)
  have hPair : Summable (pair r) := hEven.add hOdd
  have hTailEq : (∑' k, pair r k) = ∑' n, realTerm r (n + 1) := by
    unfold pair
    rw [hEven.tsum_add hOdd]
    exact tsum_even_add_odd (f := fun n => realTerm r (n + 1)) hEven hOdd
  have hNonpos : (∑' j : ℕ, pair r (j + 1)) ≤ 0 :=
    tsum_nonpos (fun j => pair_nonpos r hr h₁ (j + 1))
  have hZero : realTerm r 0 = 1 := by simp [realTerm, negPochhammer]
  rw [hSumm.tsum_eq_zero_add, hZero, ← hTailEq, hPair.tsum_eq_zero_add]
  linarith only [pair_zero_le r hr h₁, hNonpos]

end
end ManuscriptAudit.Paper8ExteriorNegativeRadius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8ExteriorNegativeRadius.negative_radial_upper
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
