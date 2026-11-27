import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DoubledExterior
import PrimalitySheafVerification.ManuscriptAudit.Paper8InsideComplexComparison

/-!
# The two printed exterior definitions have different actual sums

On the positive radius the reciprocal series of the doubled index on p. 341
is strictly smaller than the reciprocal series with the squared product on
p. 314. A termwise product comparison proves the weak inequality for every
index. The first nonconstant term makes the inequality strict.
-/

namespace ManuscriptAudit.Paper8ExteriorDefinitionsComparison

open Paper8ExteriorNormalization (negPochhammer one_le_negPochhammer)
open Paper8InsideComplexAnalytic Paper8InsideComplexComparison Paper8ExteriorComplex Paper8DoubledExterior

noncomputable section

private theorem doubledTerm_re (q : ℝ) (n : ℕ) :
    (doubledExteriorTerm n (q : ℂ)).re = q ^ (n * (n + 1)) / negPochhammer q (2 * n) := by
  rw [doubledExteriorTerm, pochhammer_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    Complex.ofReal_re]

private theorem squaredTerm_re (q : ℝ) (n : ℕ) :
    (exteriorTerm n (q : ℂ)).re = q ^ n / negPochhammer q n ^ 2 := by
  rw [exteriorTerm, pochhammer_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_div, Complex.ofReal_re]

theorem doubled_term_re_le_squared {q : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (n : ℕ) :
    (doubledExteriorTerm n (q : ℂ)).re ≤ (exteriorTerm n (q : ℂ)).re := by
  rw [doubledTerm_re, squaredTerm_re]
  let T : ℝ := ∏ j ∈ Finset.range n, (1 + q ^ (n + j + 1))
  have hSplit : negPochhammer q (2 * n) = negPochhammer q n * T := by
    simp only [T, negPochhammer, two_mul, Finset.prod_range_add, Nat.add_assoc]
  have hPowOne : q ^ n ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hq h₁ n
  have hTail : q ^ (n ^ 2) * negPochhammer q n ≤ T := by
    calc
      _ = ∏ j ∈ Finset.range n, (q ^ n * (1 + q ^ (j + 1))) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
          pow_two, negPochhammer]
      _ ≤ T := by
        apply Finset.prod_le_prod (fun j _ => by positivity)
        intro j _
        calc
          _ = q ^ n + q ^ (n + j + 1) := by rw [mul_add, mul_one, ← pow_add, Nat.add_assoc]
          _ ≤ _ := add_le_add_right hPowOne _
  have hPN : 0 < negPochhammer q n := zero_lt_one.trans_le (one_le_negPochhammer hq n)
  have hP2 : 0 < negPochhammer q (2 * n) :=
    zero_lt_one.trans_le (one_le_negPochhammer hq (2 * n))
  have hDen : q ^ (n ^ 2) * negPochhammer q n ^ 2 ≤ negPochhammer q (2 * n) := by
    calc
      _ = (q ^ (n ^ 2) * negPochhammer q n) * negPochhammer q n := by ring
      _ ≤ T * negPochhammer q n := mul_le_mul_of_nonneg_right hTail hPN.le
      _ = _ := by rw [hSplit, mul_comm]
  apply (div_le_div_iff₀ hP2 (sq_pos_of_pos hPN)).mpr
  rw [show n * (n + 1) = n + n ^ 2 by ring, pow_add]
  calc
    _ = q ^ n * (q ^ (n ^ 2) * negPochhammer q n ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hDen (pow_nonneg hq n)

theorem doubled_first_term_re_lt_squared {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    (doubledExteriorTerm 1 (q : ℂ)).re < (exteriorTerm 1 (q : ℂ)).re := by
  rw [doubledTerm_re, squaredTerm_re]
  change q ^ 2 / negPochhammer q 2 < q / negPochhammer q 1 ^ 2
  have hP₁ : negPochhammer q 1 = 1 + q := by
    simp [negPochhammer, Finset.prod_range_succ]
  have hP₂ : negPochhammer q 2 = (1 + q) * (1 + q ^ 2) := by
    simp [negPochhammer, Finset.prod_range_succ]
  rw [hP₁, hP₂]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have hLt : q * (1 + q) < 1 + q ^ 2 := by nlinarith only [h₁]
  calc
    _ = (q * (1 + q)) * (q * (1 + q)) := by ring
    _ < (1 + q ^ 2) * (q * (1 + q)) := mul_lt_mul_of_pos_right hLt (by positivity)
    _ = _ := by ring

theorem doubledExterior_re_lt_squared {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    (doubledExterior (q : ℂ)).re < (exterior (q : ℂ)).re := by
  have hNorm : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using h₁
  have hD := Complex.reCLM.hasSum (doubledExterior_absolute_summability hNorm).of_norm.hasSum
  have hS := Complex.reCLM.hasSum (exterior_absolute_summability hNorm).of_norm.hasSum
  change HasSum (fun n => (doubledExteriorTerm n (q : ℂ)).re) (doubledExterior (q : ℂ)).re at hD
  change HasSum (fun n => (exteriorTerm n (q : ℂ)).re) (exterior (q : ℂ)).re at hS
  exact hasSum_lt (doubled_term_re_le_squared hq.le h₁.le)
    (doubled_first_term_re_lt_squared hq h₁) hD hS

theorem reciprocal_printed_re_lt_standard {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    (printed (q : ℂ)⁻¹).re < (standard (q : ℂ)⁻¹).re := by
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNorm : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using h₁
  rw [printed_inv_eq_doubledExterior hq₀ hNorm, standard_inv_eq_exterior hq₀ hNorm]
  exact doubledExterior_re_lt_squared hq h₁

end
end ManuscriptAudit.Paper8ExteriorDefinitionsComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorDefinitionsComparison.doubled_term_re_le_squared,
      ``ManuscriptAudit.Paper8ExteriorDefinitionsComparison.doubled_first_term_re_lt_squared,
      ``ManuscriptAudit.Paper8ExteriorDefinitionsComparison.doubledExterior_re_lt_squared,
      ``ManuscriptAudit.Paper8ExteriorDefinitionsComparison.reciprocal_printed_re_lt_standard] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
