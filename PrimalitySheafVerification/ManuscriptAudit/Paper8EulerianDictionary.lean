import Lean.Util.CollectAxioms
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianCharacter
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianPentagonal
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianRecurrenceBridge
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorProductCorrection

/-!
# The Eulerian dictionary on the positive radius

The literal Eulerian series on p. 335 equals twice the actual positive-index
Kronecker partial theta at the reciprocal argument. This identity is separate
from the page's plus-sign formula for the ordinary squared-denominator series.
-/

namespace ManuscriptAudit.Paper8EulerianDictionary

open Paper8ExteriorNormalization (partialThetaTerm kroneckerNegTwelve)
open Paper8ExteriorProductCorrection (unilateralTheta unilateralTheta_summable_abs)
open Paper8EulerianCharacter Paper8EulerianPentagonal Paper8EulerianRecurrenceBridge
open Paper8EulerianExterior

noncomputable section

private def literalTerm (q : ℝ) (n : ℕ) : ℝ := partialThetaTerm q ((n + 1 : ℕ) : ℤ)

private theorem first_residue_term (q : ℝ) (n : ℕ) :
    literalTerm q (n * 6) = q ^ exponent n := by
  have hMod : (n * 6 + 1) % 6 = 1 := by omega
  have hChi : kroneckerNegTwelve ((n * 6 + 1 : ℕ) : ℤ) = 1 := by
    rw [kronecker_nat_mod6, if_pos hMod]
  have hCast : (((((n * 6 + 1 : ℕ) : ℝ) ^ 2) - 1) / 24) = (exponent n : ℝ) := by
    have hExp := congrArg (fun k : ℕ => (k : ℝ)) (twice_exponent n)
    push_cast at hExp ⊢
    linear_combination (-(1 / 2 : ℝ)) * hExp
  rw [literalTerm, partialThetaTerm, hChi, Int.cast_one, one_mul, Int.cast_natCast,
    hCast, Real.rpow_natCast]

private theorem second_residue_term (q : ℝ) (n : ℕ) :
    literalTerm q (n * 6 + 4) = -(q ^ (exponent n + (2 * n + 1))) := by
  have hMod : (n * 6 + 4 + 1) % 6 = 5 := by omega
  have hNotOne : (n * 6 + 4 + 1) % 6 ≠ 1 := by omega
  have hChi : kroneckerNegTwelve ((n * 6 + 4 + 1 : ℕ) : ℤ) = -1 := by
    rw [kronecker_nat_mod6, if_neg hNotOne, if_pos hMod]
  have hCast : (((((n * 6 + 4 + 1 : ℕ) : ℝ) ^ 2) - 1) / 24) =
      ((exponent n + (2 * n + 1) : ℕ) : ℝ) := by
    have hExp := congrArg (fun k : ℕ => (k : ℝ)) (twice_exponent n)
    push_cast at hExp ⊢
    linear_combination (-(1 / 2 : ℝ)) * hExp
  rw [literalTerm, partialThetaTerm, hChi, Int.cast_neg, Int.cast_one, neg_one_mul,
    Int.cast_natCast, hCast, Real.rpow_natCast]

private theorem other_residue_term (q : ℝ) (n : ℕ) (j : Fin 6)
    (h0 : j ≠ 0) (h4 : j ≠ 4) : literalTerm q (n * 6 + (j : ℕ)) = 0 := by
  have hLt := j.isLt
  have hj0 : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
  have hj4 : (j : ℕ) ≠ 4 := fun h => h4 (Fin.ext h)
  have hMod1 : (n * 6 + (j : ℕ) + 1) % 6 ≠ 1 := by omega
  have hMod5 : (n * 6 + (j : ℕ) + 1) % 6 ≠ 5 := by omega
  have hChi : kroneckerNegTwelve ((n * 6 + (j : ℕ) + 1 : ℕ) : ℤ) = 0 := by
    rw [kronecker_nat_mod6, if_neg hMod1, if_neg hMod5]
  rw [literalTerm, partialThetaTerm, hChi, Int.cast_zero, zero_mul]

private theorem sum_residue_block (q : ℝ) (n : ℕ) :
    (∑ j : Fin 6, literalTerm q (n * 6 + (j : ℕ))) = pentagonalTerm q n := by
  have hEach (j : Fin 6) : literalTerm q (n * 6 + (j : ℕ)) =
      (if j = 0 then q ^ exponent n else 0) +
        (if j = 4 then -(q ^ (exponent n + (2 * n + 1))) else 0) := by
    by_cases h0 : j = 0
    · subst j
      simpa using first_residue_term q n
    by_cases h4 : j = 4
    · subst j
      simpa using second_residue_term q n
    · simp only [h0, h4, if_false, zero_add, other_residue_term q n j h0 h4]
  simp_rw [hEach]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, pentagonalTerm, pow_add]
  ring

theorem unilateralTheta_eq_pentagonalSeries {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    unilateralTheta q = pentagonalSeries q := by
  have hNorm : Summable (fun n => ‖literalTerm q n‖) := by
    simpa only [literalTerm, Real.norm_eq_abs] using unilateralTheta_summable_abs hq h₁
  let e : ℕ ≃ ℕ × Fin 6 := Nat.divModEquiv 6
  have hGroup : Summable (fun p : ℕ × Fin 6 => literalTerm q (e.symm p)) :=
    hNorm.of_norm.comp_injective e.symm.injective
  calc
    unilateralTheta q = ∑' p : ℕ × Fin 6, literalTerm q (e.symm p) :=
      (e.symm.tsum_eq (literalTerm q)).symm
    _ = ∑' k : ℕ, ∑' j : Fin 6, literalTerm q (k * 6 + (j : ℕ)) := by
      rw [hGroup.tsum_prod] <;> rfl
    _ = pentagonalSeries q := by
      unfold pentagonalSeries
      refine tsum_congr fun n => ?_
      rw [tsum_fintype]
      exact sum_residue_block q n

theorem paper8_p335_Eulerian_dictionary_positive {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    Paper8EulerianExterior.star (q : ℂ)⁻¹ = 2 * (unilateralTheta q : ℂ) := by
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNorm : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using h₁
  rw [star_inv_eq_reciprocalStar hq₀ hNorm, reciprocalStar_ofReal_eq_two_H hq.le h₁,
    H_one_eq_pentagonalSeries hq.le h₁, ← unilateralTheta_eq_pentagonalSeries hq h₁]

end
end ManuscriptAudit.Paper8EulerianDictionary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EulerianDictionary.unilateralTheta_eq_pentagonalSeries,
      ``ManuscriptAudit.Paper8EulerianDictionary.paper8_p335_Eulerian_dictionary_positive] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
