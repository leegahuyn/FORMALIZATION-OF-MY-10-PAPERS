import Lean.Util.CollectAxioms
import Mathlib.RingTheory.RootsOfUnity.Complex
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalCommonFourier

/-!
# Exact frequency averages of the printed reciprocal contour rows

The actual modulus root has order 2k. As one ranges over a whole
frequency period, every nonzero residue contribution vanishes.
The all-residue mean is the single d = 0 term and the reduced mean
is zero. These are finite arithmetic cancellations within a row.
-/

namespace ManuscriptAudit.Paper8ShiftedRowOrthogonality

open Paper8LocalContour (root root_eq_literal)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8ContourGammaSeries (coefficient)
open Paper8ContourResidueWeights (dedekindSum sawtooth firstPhase prefactor
  residueWeight reducedResidues)
open Paper8ReciprocalCommonFourier (fourierCoefficient)

noncomputable section

theorem root_is_primitive {k : ℕ} (hk : 0 < k) : IsPrimitiveRoot (root k) (2 * k) := by
  rw [root_eq_literal hk, periodCoefficient]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    Complex.isPrimitiveRoot_exp (2 * k) (Nat.mul_pos (by decide) hk).ne'

def rootFrequency (k : ℕ) (d : Fin (2 * k)) : ℂ := (root k ^ (d.val : ℤ))⁻¹

theorem rootFrequency_pow_modulus {k : ℕ} (hk : 0 < k) (d : Fin (2 * k)) :
    rootFrequency k d ^ (2 * k) = 1 := by
  rw [rootFrequency, zpow_natCast, inv_pow, ← pow_mul, Nat.mul_comm d.val (2 * k),
    pow_mul, (root_is_primitive hk).pow_eq_one, one_pow, inv_one]

theorem rootFrequency_eq_one_iff_zero {k : ℕ} (hk : 0 < k) (d : Fin (2 * k)) :
    rootFrequency k d = 1 ↔ d.val = 0 := by
  constructor
  · intro h
    rw [rootFrequency, zpow_natCast] at h
    have hd := (root_is_primitive hk).dvd_of_pow_eq_one d.val (inv_eq_one.mp h)
    exact Nat.eq_zero_of_dvd_of_lt hd d.isLt
  · intro hd
    simp [rootFrequency, hd]

theorem geom_sum_eq {u : ℂ} {m : ℕ} (h : u ^ m = 1) :
    (∑ n ∈ Finset.range m, u ^ n) = if u = 1 then (m : ℂ) else 0 := by
  by_cases hu : u = 1
  · simp [hu]
  · rw [if_neg hu]
    apply eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero.mpr (Ne.symm hu))
    rw [mul_neg_geom_sum, h, sub_self]

theorem rootFrequency_sum_powers {k : ℕ} (hk : 0 < k) (d : Fin (2 * k)) :
    (∑ n ∈ Finset.range (2 * k), rootFrequency k d ^ n) =
      if d.val = 0 then ((2 * k : ℕ) : ℂ) else 0 := by
  rw [geom_sum_eq (rootFrequency_pow_modulus hk d), rootFrequency_eq_one_iff_zero hk d]

def shiftedInput (k : ℕ) (d : Fin (2 * k)) : ℂ :=
  -prefactor k * (residueWeight k d * (rootFrequency k d * (coefficient k 0 : ℂ)))

theorem fourierCoefficient_eq_sum_inputs (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k n : ℕ) :
    fourierCoefficient S k n =
      ∑ d ∈ S k, shiftedInput k d * rootFrequency k d ^ n := by
  unfold fourierCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  unfold shiftedInput rootFrequency
  ring

theorem shifted_row_periodic (S : ∀ k : ℕ, Finset (Fin (2 * k)))
    {k : ℕ} (hk : 0 < k) (n : ℕ) :
    fourierCoefficient S k (n + 2 * k) = fourierCoefficient S k n := by
  simp only [fourierCoefficient_eq_sum_inputs, pow_add, rootFrequency_pow_modulus hk, mul_one]

theorem shifted_row_period_sum (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) :
    (∑ n ∈ Finset.range (2 * k), fourierCoefficient S k n) =
      ∑ d ∈ S k, if d.val = 0 then ((2 * k : ℕ) : ℂ) * shiftedInput k d else 0 := by
  simp only [fourierCoefficient_eq_sum_inputs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum, rootFrequency_sum_powers hk d]
  split_ifs <;> ring

theorem reduced_row_period_sum_zero {k : ℕ} (hk : 0 < k) :
    (∑ n ∈ Finset.range (2 * k), fourierCoefficient reducedResidues k n) = 0 := by
  rw [shifted_row_period_sum reducedResidues hk]
  refine Finset.sum_eq_zero fun d hd => ?_
  apply if_neg
  intro h0
  have hC : Nat.Coprime d.val (2 * k) := (Finset.mem_filter.mp hd).2
  have hM : 2 * k = 1 := by
    simpa only [h0, Nat.Coprime, Nat.gcd_zero_left] using hC
  omega

theorem all_row_period_sum {k : ℕ} (hk : 0 < k) :
    (∑ n ∈ Finset.range (2 * k), fourierCoefficient (fun _ => Finset.univ) k n) =
      ((2 * k : ℕ) : ℂ) * (-prefactor k * (coefficient k 0 : ℂ)) := by
  let z : Fin (2 * k) := ⟨0, Nat.mul_pos (by decide) hk⟩
  rw [shifted_row_period_sum (fun _ => Finset.univ) hk]
  rw [Finset.sum_eq_single_of_mem z (Finset.mem_univ _) (fun d _ hn => by
    exact if_neg fun hd => hn (Fin.ext hd))]
  have hZ : z.val = 0 := rfl
  have hDed : dedekindSum 0 (2 * k) = 0 := by simp [dedekindSum, sawtooth]
  simp [hZ, shiftedInput, rootFrequency, residueWeight, firstPhase, hDed]

end
end ManuscriptAudit.Paper8ShiftedRowOrthogonality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ShiftedRowOrthogonality.root_is_primitive,
      ``ManuscriptAudit.Paper8ShiftedRowOrthogonality.shifted_row_periodic,
      ``ManuscriptAudit.Paper8ShiftedRowOrthogonality.shifted_row_period_sum,
      ``ManuscriptAudit.Paper8ShiftedRowOrthogonality.reduced_row_period_sum_zero,
      ``ManuscriptAudit.Paper8ShiftedRowOrthogonality.all_row_period_sum] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
