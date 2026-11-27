import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8AllResidueDivisorSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalArithmeticRows
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdOrderedLimit

/-!
# Odd-gcd arithmetic rows are scalar multiples of the reduced contour rows

This module combines the finite Dedekind/root-of-unity normalization
with the exact odd-gcd phase and Gamma leading coefficient rescaling.
-/

namespace ManuscriptAudit.Paper8OddGcdArithmeticRows

open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8ContourResidueWeights (dedekindSum reducedResidues prefactor)
open Paper8ContourGammaSeries (coefficient)
open Paper8ReciprocalCommonFourier (fourierCoefficient)
open Paper8ReciprocalArithmeticRows (shiftedFrequency arithmeticSum fourierCoefficient_eq_arithmeticSum)
open Paper8GcdArithmeticWeight (frequencyWeight)
open Paper8AllResidueDivisorSum (reducedFrequencySum)
open Paper8OddGcdResiduePhase (oddFactorSign residuePhase odd_gcd_prefactor_mul_phase)
open Paper8OddGcdOrderedLimit (oddScale odd_prefactor_coefficient_rescale)

noncomputable section

theorem arithmetic_sum_eq_reduced_frequency_sum (ℓ : ℕ) (u : ℝ) :
    arithmeticSum reducedResidues ℓ u = reducedFrequencySum (2 * ℓ) u := by
  unfold arithmeticSum reducedResidues reducedFrequencySum frequencyWeight
  simp only [Nat.cast_mul, Nat.cast_ofNat]

private theorem frequency_shift_at_even_denominator (g ℓ n : ℕ) (hℓ : 0 < ℓ)
    (d : Fin (2 * ℓ)) :
    frequencyWeight (2 * ℓ) (shiftedFrequency (g * ℓ) n) d =
      frequencyWeight (2 * ℓ) (-(n : ℝ)) d * residuePhase (g * ℓ) (g * d.val) := by
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hSc :
      (dedekindSum (-(d.val : ℤ)) (2 * ℓ) : ℝ) / 2 +
        shiftedFrequency (g * ℓ) n * (d.val : ℝ) / ((2 * ℓ : ℕ) : ℝ) =
      ((dedekindSum (-(d.val : ℤ)) (2 * ℓ) : ℝ) / 2 +
        -(n : ℝ) * (d.val : ℝ) / ((2 * ℓ : ℕ) : ℝ)) +
      (-((g * d.val : ℕ) : ℝ) / 8 * (1 + (-1 : ℝ) ^ (g * ℓ))) := by
    unfold shiftedFrequency
    push_cast
    field_simp [hℓR] <;> ring
  unfold frequencyWeight residuePhase
  rw [hSc, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem odd_of_even_coprime {m d : ℕ} (hm : Even m) (hd : Nat.Coprime d m) :
    Odd d := by
  rcases Nat.even_or_odd d with h | h
  · obtain ⟨x, hx⟩ := h
    obtain ⟨y, hy⟩ := hm
    have hDiv : 2 ∣ Nat.gcd d m := Nat.dvd_gcd ⟨x, by omega⟩ ⟨y, by omega⟩
    rw [show Nat.gcd d m = 1 from hd] at hDiv
    obtain ⟨z, hz⟩ := hDiv
    omega
  · exact h

theorem odd_residue_class_fourier_rescale {g ℓ : ℕ} (hg : Odd g) (hℓ : 0 < ℓ) (n : ℕ) :
    -prefactor (g * ℓ) * ((coefficient (g * ℓ) 0 : ℂ) *
      reducedFrequencySum (2 * ℓ) (shiftedFrequency (g * ℓ) n)) =
      oddScale g * fourierCoefficient reducedResidues ℓ n := by
  rw [fourierCoefficient_eq_arithmeticSum reducedResidues hℓ n,
    arithmetic_sum_eq_reduced_frequency_sum]
  unfold reducedFrequencySum
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hD : Odd d.val :=
    odd_of_even_coprime ⟨ℓ, by omega⟩ (Finset.mem_filter.mp hd).2
  have hS := odd_gcd_prefactor_mul_phase hg hℓ hD
  have hC := odd_prefactor_coefficient_rescale hg hℓ
  have hBase := frequency_shift_at_even_denominator 1 ℓ n hℓ d
  simp only [one_mul] at hBase
  rw [frequency_shift_at_even_denominator g ℓ n hℓ d, hBase]
  calc
    _ = -(prefactor (g * ℓ) * residuePhase (g * ℓ) (g * d.val)) *
        (coefficient (g * ℓ) 0 : ℂ) * frequencyWeight (2 * ℓ) (-(n : ℝ)) d := by ring
    _ = -(prefactor ℓ * residuePhase ℓ d.val) *
        ((oddFactorSign g / (g : ℂ)) * (coefficient (g * ℓ) 0 : ℂ)) *
        frequencyWeight (2 * ℓ) (-(n : ℝ)) d := by rw [hS]; ring
    _ = _ := by rw [hC]; ring

end
end ManuscriptAudit.Paper8OddGcdArithmeticRows

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddGcdArithmeticRows.arithmetic_sum_eq_reduced_frequency_sum,
      ``ManuscriptAudit.Paper8OddGcdArithmeticRows.odd_residue_class_fourier_rescale] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
