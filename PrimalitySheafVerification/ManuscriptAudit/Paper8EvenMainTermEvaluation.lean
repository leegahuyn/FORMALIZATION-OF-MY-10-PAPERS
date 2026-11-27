import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenMainTermFormula

/-!
# Evaluation for the candidate square-root progression constants

The coefficients are kept explicit here. If the two even constants
are C/6 and the two odd constants C/3, the exact signed combination
has strictly positive real part for 0<C.
-/

namespace ManuscriptAudit.Paper8EvenMainTermEvaluation

open Paper8EvenDenominatorWeightLimits
open Paper8EvenMainTermFormula (four_progression_main_term)

noncomputable section

private theorem inversePower_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    inversePower (a * b) = inversePower a * inversePower b := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  unfold inversePower
  rw [Nat.cast_mul, Real.mul_rpow haR.le hbR.le, ← Complex.ofReal_mul]
  congr 1
  field_simp [(Real.rpow_pos_of_pos haR (3 / 2 : ℝ)).ne',
    (Real.rpow_pos_of_pos hbR (3 / 2 : ℝ)).ne'] <;> ring

private theorem real_weight_summable :
    Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :=
  (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 (by norm_num))

theorem alternatingWeight_eq :
    alternatingWeight = (2 * inversePower 2 - 1) * zetaWeight := by
  let f (j : ℕ) := inversePower (j + 1)
  let g (j : ℕ) := (-1 : ℂ) ^ (j + 1) * f j
  have hF : Summable f := Complex.summable_ofReal.mpr real_weight_summable
  have hE : Function.Injective (fun j : ℕ => 2 * j) :=
    mul_right_injective₀ (by decide : (2 : ℕ) ≠ 0)
  have hO : Function.Injective (fun j : ℕ => 2 * j + 1) :=
    (add_left_injective 1).comp hE
  have he := hF.comp_injective hE
  have ho := hF.comp_injective hO
  have hEven (j : ℕ) : g (2 * j + 1) = f (2 * j + 1) := by
    have h : Even (2 * j + 1 + 1) := ⟨j + 1, by omega⟩
    simp only [g, h.neg_one_pow, one_mul]
  have hOdd (j : ℕ) : g (2 * j) = -f (2 * j) := by
    have h : Odd (2 * j + 1) := ⟨j, by omega⟩
    simp only [g, h.neg_one_pow, neg_one_mul]
  have hge : Summable (fun j : ℕ => g (2 * j)) := he.neg.congr (fun j => (hOdd j).symm)
  have hgo : Summable (fun j : ℕ => g (2 * j + 1)) := ho.congr (fun j => (hEven j).symm)
  have hZ : (∑' j : ℕ, f (2 * j)) + (∑' j : ℕ, f (2 * j + 1)) = zetaWeight :=
    tsum_even_add_odd he ho
  have hA : (∑' j : ℕ, g (2 * j)) + (∑' j : ℕ, g (2 * j + 1)) = alternatingWeight :=
    tsum_even_add_odd hge hgo
  have hGE : (∑' j : ℕ, g (2 * j)) = -(∑' j : ℕ, f (2 * j)) := by
    rw [← tsum_neg]
    exact tsum_congr hOdd
  have hGO : (∑' j : ℕ, g (2 * j + 1)) = ∑' j : ℕ, f (2 * j + 1) :=
    tsum_congr hEven
  rw [hGE, hGO] at hA
  have hSum : (∑' j : ℕ, f (2 * j + 1)) = inversePower 2 * zetaWeight := by
    rw [zetaWeight, ← tsum_mul_left]
    refine tsum_congr (fun j => ?_)
    change inversePower (2 * j + 1 + 1) = _
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega]
    exact inversePower_mul (by decide) (Nat.succ_pos j)
  linear_combination -hA - hZ + 2 * hSum

private def twoWeightReal : ℝ := 1 / (2 : ℝ) ^ (3 / 2 : ℝ)

private theorem twoWeightReal_pos : 0 < twoWeightReal := by
  unfold twoWeightReal
  positivity

private theorem twoWeightReal_sq : twoWeightReal * twoWeightReal = 1 / 8 := by
  have hPos : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hPow : (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), show (3 / 2 : ℝ) + 3 / 2 = (3 : ℕ) by norm_num,
      Real.rpow_natCast]
    norm_num
  unfold twoWeightReal
  rw [div_mul_div_comm, hPow, one_mul]

private theorem twoWeightReal_lt_half : twoWeightReal < 1 / 2 := by
  by_contra! h
  have hh := mul_le_mul h h (by norm_num : (0 : ℝ) ≤ 1 / 2) twoWeightReal_pos.le
  linarith [twoWeightReal_sq]

private theorem inversePower_two_sq : inversePower 2 * inversePower 2 = 1 / 8 := by
  change ((twoWeightReal : ℂ) * (twoWeightReal : ℂ)) = 1 / 8
  rw [← Complex.ofReal_mul, twoWeightReal_sq]
  push_cast <;> norm_num

theorem zetaWeight_real_part_pos : 0 < zetaWeight.re := by
  unfold zetaWeight
  change 0 < (∑' j : ℕ, ((1 / ((j + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ)).re
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  exact real_weight_summable.tsum_pos (fun _ => by positivity) 0 (by positivity)

theorem candidate_profile_combination (C : ℂ) (A : ℕ → ℂ)
    (h0 : A 0 = C / 6) (h2 : A 2 = C / 6)
    (h1 : A 1 = C / 3) (h3 : A 3 = C / 3) :
    (∑ r ∈ Finset.range 4, evenWeightLimit r * A r) =
      C * zetaWeight * (1 - 2 * inversePower 2) / 6 := by
  rw [four_progression_main_term, h0, h2, h1, h3, alternatingWeight_eq]
  linear_combination (4 / 3 : ℂ) * C * zetaWeight * inversePower_two_sq

theorem candidate_profile_combination_pos (C : ℝ) (hC : 0 < C) (A : ℕ → ℂ)
    (h0 : A 0 = (C : ℂ) / 6) (h2 : A 2 = (C : ℂ) / 6)
    (h1 : A 1 = (C : ℂ) / 3) (h3 : A 3 = (C : ℂ) / 3) :
    0 < (∑ r ∈ Finset.range 4, evenWeightLimit r * A r).re := by
  rw [candidate_profile_combination (C : ℂ) A h0 h2 h1 h3]
  have hPos : 0 < (1 - 2 * twoWeightReal) := by linarith [twoWeightReal_lt_half]
  have hRe : ((C : ℂ) * zetaWeight * (1 - 2 * inversePower 2) / 6).re =
      C * zetaWeight.re * (1 - 2 * twoWeightReal) / 6 := by
    change ((C : ℂ) * zetaWeight * (1 - 2 * (twoWeightReal : ℂ)) / 6).re = _
    rw [show (6 : ℂ) = ((6 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  rw [hRe]
  exact div_pos (mul_pos (mul_pos hC zetaWeight_real_part_pos) hPos) (by norm_num)

end
end ManuscriptAudit.Paper8EvenMainTermEvaluation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenMainTermEvaluation.alternatingWeight_eq,
      ``ManuscriptAudit.Paper8EvenMainTermEvaluation.zetaWeight_real_part_pos,
      ``ManuscriptAudit.Paper8EvenMainTermEvaluation.candidate_profile_combination,
      ``ManuscriptAudit.Paper8EvenMainTermEvaluation.candidate_profile_combination_pos] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
