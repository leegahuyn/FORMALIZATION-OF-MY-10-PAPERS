import Lean.Util.CollectAxioms
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianCharacter
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianComplexPentagonal
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadowPhase

/-! The actual p. 335 Eulerian identity for every nonzero complex point in the unit disk. -/

namespace ManuscriptAudit.Paper8EulerianComplexDictionary

open Filter Paper8ExteriorNormalization (kroneckerNegTwelve)
open Paper8EulerianCharacter Paper8EulerianComplexPentagonal Paper8EulerianExterior
open Paper8EulerianPentagonal (exponent twice_exponent)
open Paper8KroneckerShadowPhase (coefficient_square_mod_twentyFour)

noncomputable section

def powerIndex (n : ℕ) : ℕ := ((n + 1) ^ 2 - 1) / 24

def literalTerm (q : ℂ) (n : ℕ) : ℂ :=
  (kroneckerNegTwelve ((n + 1 : ℕ) : ℤ) : ℂ) * q ^ ((((n + 1 : ℕ) : ℂ) ^ 2 - 1) / 24)

def literalPsi (q : ℂ) : ℂ := ∑' n : ℕ, literalTerm q n

private def canonicalTerm (q : ℂ) (n : ℕ) : ℂ :=
  (kroneckerNegTwelve ((n + 1 : ℕ) : ℤ) : ℂ) * q ^ powerIndex n

theorem literalTerm_eq_natural_power (q : ℂ) (n : ℕ) :
    literalTerm q n = canonicalTerm q n := by
  by_cases hChi : kroneckerNegTwelve ((n + 1 : ℕ) : ℤ) = 0
  · simp [literalTerm, canonicalTerm, hChi]
  have hC : Paper8KroneckerShadow.coefficient (n + 1) ≠ 0 := by
    unfold Paper8KroneckerShadow.coefficient
    exact mul_ne_zero (by exact_mod_cast hChi) (by exact_mod_cast Nat.succ_ne_zero n)
  have hMod := coefficient_square_mod_twentyFour hC
  have hNat := Nat.mod_add_div ((n + 1) ^ 2) 24
  have hEq : (n + 1) ^ 2 = 24 * powerIndex n + 1 := by
    unfold powerIndex
    omega
  have hExp : ((((n + 1 : ℕ) : ℂ) ^ 2 - 1) / 24) = (powerIndex n : ℂ) := by
    have h := congrArg (fun k : ℕ => (k : ℂ)) hEq
    push_cast at h
    linear_combination h / 24
  rw [literalTerm, canonicalTerm, hExp, Complex.cpow_natCast]

private theorem index_ge {n : ℕ} (hn : 22 ≤ n) : n ≤ powerIndex n := by
  unfold powerIndex
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 24)).mpr
  rw [show (n + 1) ^ 2 = n * (n + 2) + 1 by ring, Nat.add_sub_cancel]
  exact Nat.mul_le_mul_left n (by omega)

private theorem kronecker_norm_nat_le_one (m : ℕ) :
    ‖(kroneckerNegTwelve (m : ℤ) : ℂ)‖ ≤ 1 := by
  rw [kronecker_nat_mod6]
  split_ifs <;> norm_num

theorem literalPsi_absolute_summability {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖literalTerm q n‖) := by
  refine (summable_geometric_of_lt_one (norm_nonneg q) hq).of_norm_bounded_eventually_nat ?_
  refine eventually_atTop.2 ⟨22, fun n hn => ?_⟩
  rw [Real.norm_of_nonneg (norm_nonneg _), literalTerm_eq_natural_power, canonicalTerm,
    norm_mul, norm_pow]
  calc
    _ ≤ 1 * ‖q‖ ^ powerIndex n :=
      mul_le_mul_of_nonneg_right (kronecker_norm_nat_le_one (n + 1)) (pow_nonneg (norm_nonneg q) _)
    _ ≤ _ := by
      simpa only [one_mul] using pow_le_pow_of_le_one (norm_nonneg q) hq.le (index_ge hn)

private theorem exponent_times_twentyFour (k : ℕ) :
    24 * exponent k = 12 * (k * (3 * k + 1)) := by
  calc
    _ = 12 * (2 * exponent k) := by ring
    _ = _ := congrArg (fun n : ℕ => 12 * n) (twice_exponent k)

private theorem first_index (k : ℕ) : powerIndex (k * 6) = exponent k := by
  unfold powerIndex
  rw [show (k * 6 + 1) ^ 2 = 12 * (k * (3 * k + 1)) + 1 by ring,
    ← exponent_times_twentyFour k]
  omega

private theorem second_index (k : ℕ) :
    powerIndex (k * 6 + 4) = exponent k + (2 * k + 1) := by
  unfold powerIndex
  rw [show (k * 6 + 4 + 1) ^ 2 = 12 * (k * (3 * k + 1)) + 24 * (2 * k + 1) + 1 by ring,
    ← exponent_times_twentyFour k]
  omega

private theorem canonical_first (q : ℂ) (k : ℕ) :
    canonicalTerm q (k * 6) = q ^ exponent k := by
  have h : (k * 6 + 1) % 6 = 1 := by omega
  have hChi : kroneckerNegTwelve ((k * 6 + 1 : ℕ) : ℤ) = 1 := by
    rw [kronecker_nat_mod6, if_pos h]
  rw [canonicalTerm, hChi, Int.cast_one, one_mul, first_index]

private theorem canonical_second (q : ℂ) (k : ℕ) :
    canonicalTerm q (k * 6 + 4) = -(q ^ (exponent k + (2 * k + 1))) := by
  have h : (k * 6 + 4 + 1) % 6 = 5 := by omega
  have hNotOne : (k * 6 + 4 + 1) % 6 ≠ 1 := by omega
  have hChi : kroneckerNegTwelve ((k * 6 + 4 + 1 : ℕ) : ℤ) = -1 := by
    rw [kronecker_nat_mod6, if_neg hNotOne, if_pos h]
  rw [canonicalTerm, hChi, Int.cast_neg, Int.cast_one, neg_one_mul, second_index]

private theorem canonical_other (q : ℂ) (k : ℕ) (j : Fin 6) (h0 : j ≠ 0) (h4 : j ≠ 4) :
    canonicalTerm q (k * 6 + (j : ℕ)) = 0 := by
  have hLt := j.isLt
  have hj0 : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
  have hj4 : (j : ℕ) ≠ 4 := fun h => h4 (Fin.ext h)
  have hMod1 : (k * 6 + (j : ℕ) + 1) % 6 ≠ 1 := by omega
  have hMod5 : (k * 6 + (j : ℕ) + 1) % 6 ≠ 5 := by omega
  have hChi : kroneckerNegTwelve ((k * 6 + (j : ℕ) + 1 : ℕ) : ℤ) = 0 := by
    rw [kronecker_nat_mod6, if_neg hMod1, if_neg hMod5]
  rw [canonicalTerm, hChi, Int.cast_zero, zero_mul]

private theorem residue_block (q : ℂ) (k : ℕ) :
    (∑ j : Fin 6, literalTerm q (k * 6 + (j : ℕ))) = complexTerm k q := by
  have hEach (j : Fin 6) : literalTerm q (k * 6 + (j : ℕ)) =
      (if j = 0 then q ^ exponent k else 0) +
        (if j = 4 then -(q ^ (exponent k + (2 * k + 1))) else 0) := by
    rw [literalTerm_eq_natural_power]
    by_cases h0 : j = 0
    · subst j
      simpa using canonical_first q k
    by_cases h4 : j = 4
    · subst j
      simpa using canonical_second q k
    · simp only [h0, h4, if_false, zero_add, canonical_other q k j h0 h4]
  simp_rw [hEach]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, complexTerm, pow_add]
  ring

theorem literalPsi_eq_complexSeries {q : ℂ} (hq : ‖q‖ < 1) : literalPsi q = complexSeries q := by
  let e : ℕ ≃ ℕ × Fin 6 := Nat.divModEquiv 6
  have hGroup : Summable (fun p : ℕ × Fin 6 => literalTerm q (e.symm p)) :=
    (literalPsi_absolute_summability hq).of_norm.comp_injective e.symm.injective
  calc
    literalPsi q = ∑' p : ℕ × Fin 6, literalTerm q (e.symm p) :=
      (e.symm.tsum_eq (literalTerm q)).symm
    _ = ∑' k : ℕ, ∑' j : Fin 6, literalTerm q (k * 6 + (j : ℕ)) := by
      rw [hGroup.tsum_prod] <;> rfl
    _ = complexSeries q := by
      unfold complexSeries
      refine tsum_congr fun k => ?_
      rw [tsum_fintype]
      exact residue_block q k

theorem paper8_p335_Eulerian_dictionary_complex {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    Paper8EulerianExterior.star q⁻¹ = 2 * literalPsi q := by
  rw [star_inv_eq_reciprocalStar hq₀ hq, reciprocalStar_eq_two_complexSeries hq,
    literalPsi_eq_complexSeries hq]

end
end ManuscriptAudit.Paper8EulerianComplexDictionary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EulerianComplexDictionary.literalTerm_eq_natural_power,
      ``ManuscriptAudit.Paper8EulerianComplexDictionary.literalPsi_absolute_summability,
      ``ManuscriptAudit.Paper8EulerianComplexDictionary.literalPsi_eq_complexSeries,
      ``ManuscriptAudit.Paper8EulerianComplexDictionary.paper8_p335_Eulerian_dictionary_complex] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
