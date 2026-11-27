import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ShiftedRowOrthogonality

/-! Finite Parseval identity for the actual shifted reciprocal Fourier row. -/

namespace ManuscriptAudit.Paper8ShiftedRowParseval

open Paper8LocalContour (root)
open Paper8ContourGammaSeries (coefficient coefficient_pos)
open Paper8ContourResidueWeights (prefactor residueWeight_norm)
open Paper8ContourDifferenceTerms (root_power_norm)
open Paper8ReciprocalCommonFourier (fourierCoefficient)
open Paper8ShiftedRowOrthogonality (root_is_primitive rootFrequency
  rootFrequency_pow_modulus shiftedInput fourierCoefficient_eq_sum_inputs geom_sum_eq)

noncomputable section

private theorem rootFrequency_norm (k : ℕ) (d : Fin (2 * k)) : ‖rootFrequency k d‖ = 1 := by
  rw [rootFrequency, norm_inv, root_power_norm, inv_one]

private theorem rootFrequency_injective {k : ℕ} (hk : 0 < k) : Function.Injective (rootFrequency k) := by
  intro d e h
  apply Fin.ext
  have hEq : root k ^ d.val = root k ^ e.val := by
    simp only [rootFrequency, zpow_natCast] at h
    exact inv_injective h
  exact (root_is_primitive hk).injOn_pow
    (by simpa only [Finset.mem_coe, Finset.mem_range] using d.isLt)
    (by simpa only [Finset.mem_coe, Finset.mem_range] using e.isLt) hEq

private theorem rootFrequency_mul_conj (k : ℕ) (d : Fin (2 * k)) :
    rootFrequency k d * (starRingEnd ℂ) (rootFrequency k d) = 1 := by
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, rootFrequency_norm, one_pow,
    Complex.ofReal_one]

theorem root_pair_sum {k : ℕ} (hk : 0 < k) (d e : Fin (2 * k)) :
    (∑ n ∈ Finset.range (2 * k), (rootFrequency k d * (starRingEnd ℂ) (rootFrequency k e)) ^ n) =
      if d = e then ((2 * k : ℕ) : ℂ) else 0 := by
  let u : ℂ := rootFrequency k d * (starRingEnd ℂ) (rootFrequency k e)
  have hPow : u ^ (2 * k) = 1 := by
    unfold u
    rw [mul_pow, rootFrequency_pow_modulus hk d, ← map_pow,
      rootFrequency_pow_modulus hk e, map_one, one_mul]
  have hOne : u = 1 ↔ d = e := by
    constructor
    · intro h
      apply rootFrequency_injective hk
      calc
        rootFrequency k d = rootFrequency k d *
            ((starRingEnd ℂ) (rootFrequency k e) * rootFrequency k e) := by
          rw [mul_comm ((starRingEnd ℂ) (rootFrequency k e)), rootFrequency_mul_conj, mul_one]
        _ = rootFrequency k e := by rw [← mul_assoc]; change u * rootFrequency k e = _; rw [h, one_mul]
    · rintro rfl
      exact rootFrequency_mul_conj k d
  change (∑ n ∈ Finset.range (2 * k), u ^ n) = _
  rw [geom_sum_eq hPow, hOne]

private theorem parseval_complex (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) :
    (∑ n ∈ Finset.range (2 * k), fourierCoefficient S k n *
      (starRingEnd ℂ) (fourierCoefficient S k n)) =
      ((2 * k : ℕ) : ℂ) * ∑ d ∈ S k, shiftedInput k d * (starRingEnd ℂ) (shiftedInput k d) := by
  have hExpand (n : ℕ) : fourierCoefficient S k n * (starRingEnd ℂ) (fourierCoefficient S k n) =
      ∑ d ∈ S k, ∑ e ∈ S k,
        (shiftedInput k d * (starRingEnd ℂ) (shiftedInput k e)) *
          (rootFrequency k d * (starRingEnd ℂ) (rootFrequency k e)) ^ n := by
    simp only [fourierCoefficient_eq_sum_inputs, map_sum, map_mul, map_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_pow]
    ring
  rw [Finset.mul_sum]
  simp_rw [hExpand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, root_pair_sum hk]
  rw [Finset.sum_eq_single_of_mem d hd (fun e _ h => by simp only [if_neg (Ne.symm h), mul_zero])]
  rw [if_pos rfl]
  ring

private theorem shiftedInput_norm {k : ℕ} (hk : 0 < k) (d : Fin (2 * k)) :
    ‖shiftedInput k d‖ = coefficient k 0 / (k : ℝ) := by
  have hCast : ‖(k : ℂ)‖ = (k : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg k)]
  simp only [shiftedInput, norm_mul, norm_neg, residueWeight_norm, rootFrequency_norm,
    Complex.norm_real, Real.norm_of_nonneg (coefficient_pos hk 0).le, prefactor, norm_div,
    norm_pow, norm_one, one_pow, hCast, one_mul]
  ring

theorem shifted_row_parseval (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) :
    (∑ n ∈ Finset.range (2 * k), ‖fourierCoefficient S k n‖ ^ 2) =
      ((2 * k : ℕ) : ℝ) * ((S k).card : ℝ) * (coefficient k 0 / (k : ℝ)) ^ 2 := by
  have h := parseval_complex S hk
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_natCast,
    ← Complex.ofReal_sum, ← Complex.ofReal_mul] at h
  calc
    _ = ((2 * k : ℕ) : ℝ) * ∑ d ∈ S k, ‖shiftedInput k d‖ ^ 2 :=
      Complex.ofReal_injective h
    _ = _ := by
      simp only [shiftedInput_norm hk, Finset.sum_const, nsmul_eq_mul]
      ring

end
end ManuscriptAudit.Paper8ShiftedRowParseval

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ShiftedRowParseval.root_pair_sum,
      ``ManuscriptAudit.Paper8ShiftedRowParseval.shifted_row_parseval] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
