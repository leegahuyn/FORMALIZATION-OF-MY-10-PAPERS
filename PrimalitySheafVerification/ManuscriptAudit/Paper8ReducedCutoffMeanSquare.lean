import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReducedRowCrossOrthogonality
import PrimalitySheafVerification.ManuscriptAudit.Paper8ShiftedRowParseval
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdOrderedLimit

/-!
# A cutoff-independent mean square over a common finite frequency period

For relatively prime residues, distinct moduli contribute disjoint
frequency characters. The average squared coefficient of the finite
modulus cutoff is the sum of the individual row energies. These
energies have a summable quadratic decay in the modulus.
-/

namespace ManuscriptAudit.Paper8ReducedCutoffMeanSquare

open Paper8ContourResidueWeights (reducedResidues)
open Paper8ContourGammaSeries (coefficient)
open Paper8ShiftedRowOrthogonality (shifted_row_periodic)
open Paper8ShiftedRowParseval (shifted_row_parseval)
open Paper8ReducedRowCrossOrthogonality (reduced_cross_row_period_sum)
open Paper8ReciprocalCommonFourier (fourierCoefficient orderedFourierCoefficient)
open Paper8OddGcdOrderedLimit (coefficient_zero_rescale)

noncomputable section

def rowEnergy (k : ℕ) : ℝ :=
  ((reducedResidues k).card : ℝ) * (coefficient k 0 / (k : ℝ)) ^ 2

private theorem sum_range_repeat (f : ℕ → ℝ) (T : ℕ) (h : ∀ n, f (n + T) = f n) (m : ℕ) :
    (∑ n ∈ Finset.range (T * m), f n) = (m : ℝ) * ∑ n ∈ Finset.range T, f n := by
  have hTr (p n : ℕ) : f (T * p + n) = f n := by
    induction p with
    | zero => simp
    | succ p ih =>
      rw [Nat.mul_succ, show T * p + T + n = (T * p + n) + T by omega, h, ih]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [hTr, Nat.cast_succ, add_mul, one_mul]

theorem row_energy_across_common_period {k M : ℕ} (hk : 0 < k) (hM : 2 * k ∣ M) :
    (∑ n ∈ Finset.range M, ‖fourierCoefficient reducedResidues k n‖ ^ 2) =
      (M : ℝ) * rowEnergy k := by
  obtain ⟨m, rfl⟩ := hM
  have h (n : ℕ) :
      ‖fourierCoefficient reducedResidues k (n + (2 * k))‖ ^ 2 =
        ‖fourierCoefficient reducedResidues k n‖ ^ 2 := by
    rw [shifted_row_periodic reducedResidues hk]
  rw [sum_range_repeat _ (2 * k) h, shifted_row_parseval reducedResidues hk, rowEnergy]
  push_cast
  ring

theorem reduced_cutoff_sum_squares (N M : ℕ)
    (hM : ∀ k ∈ Finset.range N, 2 * (k + 1) ∣ M) :
    (∑ n ∈ Finset.range M, ‖orderedFourierCoefficient reducedResidues N n‖ ^ 2) =
      (M : ℝ) * ∑ k ∈ Finset.range N, rowEnergy (k + 1) := by
  let F (k n : ℕ) := fourierCoefficient reducedResidues (k + 1) n
  let U (n : ℕ) := orderedFourierCoefficient reducedResidues N n
  have hExpand (n : ℕ) : U n * (starRingEnd ℂ) (U n) =
      ∑ k ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, F k n * (starRingEnd ℂ) (F ℓ n) := by
    simp only [U, orderedFourierCoefficient, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [F, Finset.mul_sum]
  have hC : (∑ n ∈ Finset.range M, U n * (starRingEnd ℂ) (U n)) =
      ∑ k ∈ Finset.range N, (((M : ℝ) * rowEnergy (k + 1) : ℝ) : ℂ) := by
    simp only [hExpand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single_of_mem k hk (fun ℓ hℓ hNe =>
      reduced_cross_row_period_sum (Nat.succ_pos k) (Nat.succ_pos ℓ)
        (fun he => hNe (by omega)) (hM k hk) (hM ℓ hℓ))]
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_sum]
    exact congrArg Complex.ofReal (row_energy_across_common_period (Nat.succ_pos k) (hM k hk))
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_sum] at hC
  unfold U at hC
  rw [Finset.mul_sum]
  exact Complex.ofReal_injective hC

private theorem row_energy_le {k : ℕ} (hk : 0 < k) :
    rowEnergy k ≤ (2 * (coefficient 1 0)^2) * (1 / (k : ℝ)^2) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hCardNat : (reducedResidues k).card ≤ 2 * k := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (reducedResidues k)
  have hCard : ((reducedResidues k).card : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hCardNat
  have hC := coefficient_zero_rescale hk (Nat.succ_pos 0)
  rw [Nat.mul_one] at hC
  have hSq : (coefficient k 0 / (k : ℝ)) ^ 2 = (coefficient 1 0) ^ 2 / (k : ℝ) ^ 3 := by
    rw [hC, ← Real.sqrt_eq_rpow]
    simp only [div_pow, mul_pow, one_pow, Real.sq_sqrt hkR.le]
    field_simp [hkR.ne'] <;> ring
  calc
    _ ≤ 2 * (k : ℝ) * (coefficient k 0 / (k : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hCard (sq_nonneg _)
    _ = _ := by rw [hSq]; field_simp [hkR.ne'] <;> ring

theorem reduced_cutoff_frequency_average_bounded (N : ℕ) {M : ℕ} (hPos : 0 < M)
    (hM : ∀ k ∈ Finset.range N, 2 * (k + 1) ∣ M) :
    ((∑ n ∈ Finset.range M, ‖orderedFourierCoefficient reducedResidues N n‖ ^ 2) / (M : ℝ)) ≤
      (2 * (coefficient 1 0)^2) * ∑' j : ℕ, 1 / ((j + 1 : ℕ) : ℝ)^2 := by
  have hmR : 0 < (M : ℝ) := by exact_mod_cast hPos
  rw [reduced_cutoff_sum_squares N M hM, mul_div_cancel_left₀ _ hmR.ne']
  have hBase : Summable (fun j : ℕ => (1 : ℝ) / (j : ℝ)^2) := by
    simpa only [Real.rpow_two] using
      (Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 2))
  have hSum : Summable (fun j : ℕ => (1 : ℝ) / ((j + 1 : ℕ) : ℝ)^2) :=
    (summable_nat_add_iff 1).2 hBase
  calc
    _ ≤ ∑ k ∈ Finset.range N, (2 * (coefficient 1 0)^2) * (1 / ((k + 1 : ℕ) : ℝ)^2) :=
      Finset.sum_le_sum fun k _ => row_energy_le (Nat.succ_pos k)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hSum.sum_le_tsum _ (fun _ _ => by positivity)) (by positivity)

end
end ManuscriptAudit.Paper8ReducedCutoffMeanSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReducedCutoffMeanSquare.row_energy_across_common_period,
      ``ManuscriptAudit.Paper8ReducedCutoffMeanSquare.reduced_cutoff_sum_squares,
      ``ManuscriptAudit.Paper8ReducedCutoffMeanSquare.reduced_cutoff_frequency_average_bounded] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
