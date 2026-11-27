import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorDefinitionsComparison
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplexComparison
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorProductCorrection

/-!
# A counterexample to the precise dictionary on physical p. 341

This page uses the doubled product for `f`, the positive-index Kronecker
series for `ψ`, and the triangular series without a denominator for `S`.
At the positive argument `2^(-24)` the two printed sides satisfy a strict
inequality.
-/

namespace ManuscriptAudit.Paper8DoubledDictionary

open Paper8InsideComplexAnalytic Paper8ExteriorComplexComparison Paper8ExteriorDefinitionsComparison
open Paper8ExteriorProductCorrection

noncomputable section

def standaloneCorrection (q : ℝ) : ℝ := ∑' n : ℕ, correctionNumeratorTerm q n

private theorem triangular_exponent_ge (n : ℕ) : n ≤ n * (n + 1) / 2 := by
  cases n with
  | zero => decide
  | succ n =>
      have h := Nat.mul_le_mul_left (n + 1) (show 2 ≤ n + 1 + 1 by omega)
      rw [Nat.mul_comm (n + 1) 2] at h
      omega

theorem standaloneCorrection_abs_le {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    |standaloneCorrection q| ≤ (1 - q)⁻¹ := by
  have hTerm (n : ℕ) : ‖correctionNumeratorTerm q n‖ ≤ q ^ n := by
    rw [Real.norm_eq_abs, correctionNumeratorTerm, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_nonneg (pow_nonneg hq _)]
    exact pow_le_pow_of_le_one hq h₁.le (triangular_exponent_ge n)
  simpa only [standaloneCorrection, Real.norm_eq_abs] using
    (tsum_of_norm_bounded (hasSum_geometric_of_lt_one hq h₁) hTerm)

private theorem testQ_inverse_weight :
    ((testQ : ℂ)⁻¹) ^ (-((24 : ℂ)⁻¹)) = ((1 / 2 : ℝ) : ℂ) := by
  have hq : 0 ≤ testQ := by norm_num [testQ]
  have hReal : testQ⁻¹ ^ (-(1 : ℝ) / 24) = (1 : ℝ) / 2 := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    have hExpReal : -(-(1 : ℝ) / 24) = (1 : ℝ) / 24 := by ring
    rw [hExpReal, testQ, ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (1 : ℝ) / 2) 24]
    norm_num
  have hExp : (-((24 : ℂ)⁻¹)) = ((-(1 : ℝ) / 24 : ℝ) : ℂ) := by norm_num
  rw [hExp, ← Complex.ofReal_inv, ← Complex.ofReal_cpow (inv_nonneg.mpr hq), hReal]

theorem literal_doubled_dictionary_strict :
    ((((testQ : ℂ)⁻¹) ^ (-((24 : ℂ)⁻¹))) * printed (testQ : ℂ)⁻¹).re <
      2 * unilateralTheta testQ - standaloneCorrection testQ := by
  have hq : 0 < testQ := by norm_num [testQ]
  have h₁ : testQ < 1 := by norm_num [testQ]
  have hGeo : (1 - testQ)⁻¹ < (10 : ℝ) / 9 := by norm_num [testQ]
  have hSmaller := reciprocal_printed_re_lt_standard hq h₁
  rw [standard_ofReal_inverse hq h₁, Complex.ofReal_re] at hSmaller
  have hExterior := (hSmaller.trans_le (exterior_le_geometric hq h₁)).trans hGeo
  have hS := ((le_abs_self (standaloneCorrection testQ)).trans
    (standaloneCorrection_abs_le hq.le h₁)).trans_lt hGeo
  rw [testQ_inverse_weight, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  linarith only [hExterior, hS, unilateralTheta_testQ_ge]

theorem paper8_p341_literal_dictionary_refuted :
    ((testQ : ℂ)⁻¹) ^ (-((24 : ℂ)⁻¹)) * printed (testQ : ℂ)⁻¹ ≠
      ((2 * unilateralTheta testQ - standaloneCorrection testQ : ℝ) : ℂ) := by
  intro h
  have hRe := congrArg Complex.re h
  exact literal_doubled_dictionary_strict.ne hRe

end
end ManuscriptAudit.Paper8DoubledDictionary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DoubledDictionary.standaloneCorrection_abs_le,
      ``ManuscriptAudit.Paper8DoubledDictionary.literal_doubled_dictionary_strict,
      ``ManuscriptAudit.Paper8DoubledDictionary.paper8_p341_literal_dictionary_refuted] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
