import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenGcdOrderedLimit

/-!
# Absolute convergence of every fixed reduced-denominator even subgroup

Fixing the reduced denominator D leaves the positive half-gcd h as
the summation index, with the original modulus k = hD. For every mode
this subseries has the summable h^(-3/2) majorant.
-/

namespace ManuscriptAudit.Paper8FixedEvenDenominator

open Paper8ContourGammaSeries (coefficient)
open Paper8ContourResidueWeights (prefactor dedekindSum sawtooth)
open Paper8ReciprocalArithmeticRows (shiftedFrequency)
open Paper8GcdArithmeticWeight (frequencyWeight)
open Paper8AllResidueDivisorSum (reducedFrequencySum)
open Paper8EvenGcdArithmeticRows (even_residue_class_fourier_rescale)
open Paper8EvenGcdOrderedLimit (evenWeight evenWeight_norm_summable unshiftedCoefficient)

noncomputable section

theorem fixed_even_denominator_norm_summable {D : ℕ} (hD : 0 < D) (n : ℕ) :
    Summable (fun j : ℕ => ‖-prefactor ((j + 1) * D) *
      ((coefficient ((j + 1) * D) 0 : ℂ) *
        reducedFrequencySum D (shiftedFrequency ((j + 1) * D) n))‖) := by
  apply ((evenWeight_norm_summable D).mul_right ‖unshiftedCoefficient D n‖).congr
  intro j
  rw [even_residue_class_fourier_rescale (Nat.succ_pos j) hD n, norm_mul]
  rfl

theorem reducedFrequencySum_one (u : ℝ) : reducedFrequencySum 1 u = 1 := by
  have hS : (Finset.univ.filter (fun d : Fin 1 => Nat.Coprime d.val 1)) = Finset.univ := by decide
  rw [reducedFrequencySum, hS, Fin.sum_univ_one]
  simp [frequencyWeight, dedekindSum, sawtooth]

theorem zero_residue_norm_summable :
    Summable (fun j : ℕ => ‖-prefactor (j + 1) * (coefficient (j + 1) 0 : ℂ)‖) := by
  apply (fixed_even_denominator_norm_summable (Nat.succ_pos 0) 0).congr
  intro j
  simp only [Nat.mul_one, reducedFrequencySum_one, mul_one]

end
end ManuscriptAudit.Paper8FixedEvenDenominator

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8FixedEvenDenominator.fixed_even_denominator_norm_summable,
      ``ManuscriptAudit.Paper8FixedEvenDenominator.reducedFrequencySum_one,
      ``ManuscriptAudit.Paper8FixedEvenDenominator.zero_residue_norm_summable] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
