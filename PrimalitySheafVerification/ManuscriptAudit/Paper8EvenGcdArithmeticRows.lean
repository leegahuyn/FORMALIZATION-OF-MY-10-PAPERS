import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8AllResidueDivisorSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalArithmeticRows
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdOrderedLimit
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenGcdResiduePhase

/-!
# Even-gcd arithmetic rows at the unshifted reciprocal frequency

When the gcd is 2h and the reduced modulus is D, the signed
Fourier coefficient class reduces to the unshifted frequency -n
at modulus D. The coefficient is rescaled by h^(-3/2) and a sign
determined by h and D modulo four. This is a finite identity.
-/

namespace ManuscriptAudit.Paper8EvenGcdArithmeticRows

open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8ContourResidueWeights (dedekindSum prefactor)
open Paper8ContourGammaSeries (coefficient)
open Paper8ReciprocalArithmeticRows (shiftedFrequency)
open Paper8GcdArithmeticWeight (frequencyWeight)
open Paper8AllResidueDivisorSum (reducedFrequencySum)
open Paper8OddGcdResiduePhase (modulusSign residuePhase)
open Paper8OddGcdOrderedLimit (coefficient_zero_rescale)
open Paper8EvenGcdResiduePhase (phase_of_odd_denominator combined_sign_modulus_zero_mod_four
  combined_sign_modulus_two_mod_four)

noncomputable section

def evenGcdSign (h D : ℕ) : ℂ :=
  if D % 2 = 1 then modulusSign (h * D)
  else if D % 4 = 0 then (-1 : ℂ) ^ h
  else 1

private theorem frequency_shift (h D n : ℕ) (hD : 0 < D) (d : Fin D) :
    frequencyWeight D (shiftedFrequency (h * D) n) d =
      frequencyWeight D (-(n : ℝ)) d * residuePhase (h * D) ((2 * h) * d.val) := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hSc :
      (dedekindSum (-(d.val : ℤ)) D : ℝ) / 2 +
        shiftedFrequency (h * D) n * (d.val : ℝ) / (D : ℝ) =
      ((dedekindSum (-(d.val : ℤ)) D : ℝ) / 2 +
        -(n : ℝ) * (d.val : ℝ) / (D : ℝ)) +
      (-(((2 * h) * d.val : ℕ) : ℝ) / 8 * (1 + (-1 : ℝ) ^ (h * D))) := by
    unfold shiftedFrequency
    push_cast
    field_simp [hDR] <;> ring
  unfold frequencyWeight residuePhase
  rw [hSc, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem odd_numerator_of_even_denominator {u D : ℕ} (hD : Even D)
    (hu : Nat.Coprime u D) : Odd u := by
  rcases Nat.even_or_odd u with h | h
  · obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := hD
    have hDiv : 2 ∣ Nat.gcd u D := Nat.dvd_gcd ⟨a, by omega⟩ ⟨b, by omega⟩
    rw [show Nat.gcd u D = 1 from hu] at hDiv
    obtain ⟨c, hc⟩ := hDiv
    omega
  · exact h

theorem combined_sign (h D u : ℕ) (hu : Nat.Coprime u D) :
    modulusSign (h * D) * residuePhase (h * D) ((2 * h) * u) = evenGcdSign h D := by
  rcases Nat.even_or_odd D with hD | hD
  · have hU := odd_numerator_of_even_denominator hD hu
    obtain ⟨a, ha⟩ := hD
    have hEven : ¬ D % 2 = 1 := by omega
    rcases (show D % 4 = 0 ∨ D % 4 = 2 by omega) with h₀ | h₂
    · have hEq : D = 4 * (D / 4) := by omega
      simp only [evenGcdSign, if_neg hEven, if_pos h₀]
      conv_lhs => rw [hEq]
      exact combined_sign_modulus_zero_mod_four h (D / 4) u hU
    · have hEq : D = 4 * (D / 4) + 2 := by omega
      simp only [evenGcdSign, if_neg hEven, if_neg (show D % 4 ≠ 0 by omega)]
      conv_lhs => rw [hEq]
      exact combined_sign_modulus_two_mod_four h (D / 4) u hU
  · have hOdd : D % 2 = 1 := by obtain ⟨a, ha⟩ := hD; omega
    rw [phase_of_odd_denominator h D u hD, mul_one, evenGcdSign, if_pos hOdd]

private theorem sign_reduces_mod_four (k : ℕ) : modulusSign k = modulusSign (k % 4) := by
  have h : (k + 1) / 2 = 2 * (k / 4) + ((k % 4) + 1) / 2 := by omega
  have he : Even (2 * (k / 4)) := ⟨k / 4, by omega⟩
  rw [modulusSign, modulusSign, h, pow_add, he.neg_one_pow, one_mul]

theorem sign_depends_on_mod_four (h D : ℕ) :
    evenGcdSign h D = evenGcdSign (h % 4) (D % 4) := by
  have hMod2 : (D % 4) % 2 = D % 2 := by omega
  have hMod4 : (D % 4) % 4 = D % 4 := by omega
  have hExp : h = 4 * (h / 4) + h % 4 := by omega
  have hPow : (-1 : ℂ) ^ h = (-1 : ℂ) ^ (h % 4) := by
    have he : Even (4 * (h / 4)) := ⟨2 * (h / 4), by omega⟩
    calc
      _ = (-1 : ℂ) ^ (4 * (h / 4) + h % 4) := congrArg (fun n : ℕ => (-1 : ℂ) ^ n) hExp
      _ = _ := by rw [pow_add, he.neg_one_pow, one_mul]
  have hSign : modulusSign (h * D) = modulusSign ((h % 4) * (D % 4)) := by
    rw [sign_reduces_mod_four (h * D), sign_reduces_mod_four ((h % 4) * (D % 4)),
      Nat.mul_mod h D 4]
  simp only [evenGcdSign, hMod2, hMod4, hSign, hPow]

private theorem coefficient_over_modulus_rescale {h D : ℕ} (hh : 0 < h) (hD : 0 < D) :
    (coefficient (h * D) 0 : ℂ) / ((h * D : ℕ) : ℂ) =
      ((1 / (h : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * ((coefficient D 0 : ℂ) / (D : ℂ)) := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hpow : (h : ℝ) ^ (3 / 2 : ℝ) = (h : ℝ) * (h : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hhR, Real.rpow_one]
  have hReal : coefficient (h * D) 0 / ((h * D : ℕ) : ℝ) =
      (1 / (h : ℝ) ^ (3 / 2 : ℝ)) * (coefficient D 0 / (D : ℝ)) := by
    rw [coefficient_zero_rescale hh hD, Nat.cast_mul, hpow]
    have hHalf : (h : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hhR _).ne'
    field_simp [hhR.ne', hDR.ne', hHalf] <;> ring
  exact_mod_cast hReal

theorem even_residue_class_fourier_rescale {h D : ℕ} (hh : 0 < h) (hD : 0 < D) (n : ℕ) :
    -prefactor (h * D) * ((coefficient (h * D) 0 : ℂ) *
      reducedFrequencySum D (shiftedFrequency (h * D) n)) =
      (((1 / (h : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * evenGcdSign h D) *
        (-((coefficient D 0 : ℂ) / (D : ℂ)) * reducedFrequencySum D (-(n : ℝ))) := by
  change -(modulusSign (h * D) / ((h * D : ℕ) : ℂ)) * ((coefficient (h * D) 0 : ℂ) *
    reducedFrequencySum D (shiftedFrequency (h * D) n)) = _
  unfold reducedFrequencySum
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdC : Nat.Coprime d.val D := (Finset.mem_filter.mp hd).2
  rw [frequency_shift h D n hD d]
  calc
    _ = -(modulusSign (h * D) * residuePhase (h * D) ((2 * h) * d.val)) *
      ((coefficient (h * D) 0 : ℂ) / ((h * D : ℕ) : ℂ)) *
      frequencyWeight D (-(n : ℝ)) d := by ring
    _ = _ := by
      rw [combined_sign h D d.val hdC, coefficient_over_modulus_rescale hh hD]
      ring

end
end ManuscriptAudit.Paper8EvenGcdArithmeticRows

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenGcdArithmeticRows.combined_sign,
      ``ManuscriptAudit.Paper8EvenGcdArithmeticRows.sign_depends_on_mod_four,
      ``ManuscriptAudit.Paper8EvenGcdArithmeticRows.even_residue_class_fourier_rescale] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
