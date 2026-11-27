import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourCoefficientDecay
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourResidueWeights

/-!
# The signed q¹ coefficient difference for the reduced-residue reading

The individual q¹ coefficient after the outer q is the zero-parameter
contour moment. The difference of these moments is absolutely summable
against the literal reduced residue weights. Its signed real part is
strictly positive. For an unrestricted reading the leading residue
weights differ, and its difference series is also summable.
-/

namespace ManuscriptAudit.Paper8ContourSignedCoefficient

open Paper8ContourCoefficientDecay (delta delta_eq_moments delta_one_pos delta_nonneg delta_le_decay)
open Paper8ContourSignedDominance (decay decay_tail_summable signed_coefficient_pos)
open Paper8ContourMoment (atZero atZero_literal_lt_rhoades)
open Paper8ContourResidueWeights
  (allWeight reducedWeight reducedResidues weighted_norm_le_two allWeight_one allWeight_two_re
    reducedWeight_one)

noncomputable section

theorem reduced_difference_summable_and_positive :
    Summable (fun n : ℕ => reducedWeight (n + 1) * (delta (n + 1) : ℂ)) ∧
      0 < (∑' n : ℕ, reducedWeight (n + 1) * (delta (n + 1) : ℂ)).re :=
  signed_coefficient_pos delta reducedWeight delta_one_pos delta_nonneg
    (fun _ hk => delta_le_decay hk) reducedWeight_one
    (fun k hk => weighted_norm_le_two (by omega : 0 < k) (reducedResidues k))

theorem all_difference_summable :
    Summable (fun n : ℕ => allWeight (n + 1) * (delta (n + 1) : ℂ)) := by
  have hMajorant : Summable (fun n : ℕ => (2 * delta 1) * decay (n + 2)) :=
    (decay_tail_summable 2 (by decide)).mul_left _
  have hNorm : Summable (fun n : ℕ => ‖allWeight (n + 2) * (delta (n + 2) : ℂ)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hMajorant
    intro n
    have hn : 2 ≤ n + 2 := by omega
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (delta_nonneg _)]
    calc
      _ ≤ 2 * (decay (n + 2) * delta 1) :=
        mul_le_mul (weighted_norm_le_two (by omega : 0 < n + 2) Finset.univ)
          (delta_le_decay hn) (delta_nonneg _) (by norm_num)
      _ = _ := by ring
  exact (summable_nat_add_iff 1).mp hNorm.of_norm

theorem all_first_term_zero : allWeight 1 * (delta 1 : ℂ) = 0 := by
  rw [allWeight_one, zero_mul]

theorem all_second_term_re :
    (allWeight 2 * (delta 2 : ℂ)).re = -(1 + Real.cos (Real.pi / 8)) * delta 2 := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, allWeight_two_re]

theorem all_second_term_negative : (allWeight 2 * (delta 2 : ℂ)).re < 0 := by
  rw [all_second_term_re]
  have hDelta : 0 < delta 2 := by
    rw [delta_eq_moments (by decide : 0 < (2 : ℕ)) (r := 1) zero_lt_one]
    exact sub_pos.mpr (atZero_literal_lt_rhoades (by decide : 0 < (2 : ℕ)) zero_lt_one)
  have hCos : 0 < Real.cos (Real.pi / 8) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact mul_neg_of_neg_of_pos (by linarith) hDelta

def coefficientTerm (α : ℝ) (n : ℕ) : ℂ :=
  reducedWeight (n + 1) * ((atZero α (n + 1) 1).re : ℂ)

theorem reduced_coefficients_ne_of_summable
    (hPrimary : Summable (coefficientTerm 23)) (hPrinted : Summable (coefficientTerm (2 / 3))) :
    (∑' n : ℕ, coefficientTerm 23 n) ≠ ∑' n : ℕ, coefficientTerm (2 / 3) n := by
  have hDiff (n : ℕ) :
      coefficientTerm 23 n - coefficientTerm (2 / 3) n =
        reducedWeight (n + 1) * (delta (n + 1) : ℂ) := by
    rw [delta_eq_moments (Nat.succ_pos n) (r := 1) zero_lt_one, Complex.ofReal_sub]
    unfold coefficientTerm
    ring
  have hSum : (∑' n : ℕ, reducedWeight (n + 1) * (delta (n + 1) : ℂ)) =
      (∑' n : ℕ, coefficientTerm 23 n) - ∑' n : ℕ, coefficientTerm (2 / 3) n := by
    calc
      _ = ∑' n : ℕ, (coefficientTerm 23 n - coefficientTerm (2 / 3) n) :=
        tsum_congr (fun n => (hDiff n).symm)
      _ = _ := hPrimary.tsum_sub hPrinted
  intro h
  have hPos := reduced_difference_summable_and_positive.2
  rw [hSum, h, sub_self, Complex.zero_re] at hPos
  exact lt_irrefl _ hPos

end
end ManuscriptAudit.Paper8ContourSignedCoefficient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourSignedCoefficient.reduced_difference_summable_and_positive,
      ``ManuscriptAudit.Paper8ContourSignedCoefficient.all_difference_summable,
      ``ManuscriptAudit.Paper8ContourSignedCoefficient.all_first_term_zero,
      ``ManuscriptAudit.Paper8ContourSignedCoefficient.all_second_term_re,
      ``ManuscriptAudit.Paper8ContourSignedCoefficient.all_second_term_negative,
      ``ManuscriptAudit.Paper8ContourSignedCoefficient.reduced_coefficients_ne_of_summable] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
