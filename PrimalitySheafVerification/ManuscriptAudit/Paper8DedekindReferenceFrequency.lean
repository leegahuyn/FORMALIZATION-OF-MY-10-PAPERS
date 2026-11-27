import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindZeroReference
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalArithmeticRows

/-!
# Reference normalization at every shifted Fourier frequency

At integral frequency this is Ahlgren–Andersen, arXiv:1504.02500v3,
equation (1.2). The calculation is a finite arithmetic identity.
-/

namespace ManuscriptAudit.Paper8DedekindReferenceFrequency

open Paper8ContourResidueWeights (dedekindSum prefactor reducedResidues)
open Paper8ContourGammaSeries (coefficient)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8GcdArithmeticWeight Paper8AllResidueDivisorSum Paper8DedekindZeroReference
open Paper8ReciprocalCommonFourier (fourierCoefficient)
open Paper8ReciprocalArithmeticRows

noncomputable section

def referenceSum (D : ℕ) (u : ℝ) : ℂ :=
  ∑ d ∈ (Finset.univ.filter (fun d : Fin D => Nat.Coprime d.val D)),
    Complex.exp ((Real.pi : ℂ) * Complex.I *
      (((dedekindSum (d.val : ℤ) D : ℝ) - 2*u*(d.val : ℝ)/(D : ℝ) : ℝ) : ℂ))

theorem referenceSum_at_zero (D : ℕ) : referenceSum D 0 = referenceZeroSum D := by
  simp [referenceSum, referenceZeroSum]

theorem reducedFrequencySum_eq_conj_reference (D : ℕ) (u : ℝ) :
    reducedFrequencySum D u = (starRingEnd ℂ) (referenceSum D u) := by
  unfold reducedFrequencySum referenceSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [frequencyWeight, dedekindSum_neg, Rat.cast_neg,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  rw [periodCoefficient]
  push_cast
  ring

theorem actual_reduced_fourier_reference {k : ℕ} (hk : 0 < k) (n : ℕ) :
    fourierCoefficient reducedResidues k n = -prefactor k *
      ((coefficient k 0 : ℂ) *
        (starRingEnd ℂ) (referenceSum (2*k) (shiftedFrequency k n))) := by
  rw [fourierCoefficient_eq_arithmeticSum reducedResidues hk,
    ← reducedFrequencySum_eq_conj_reference]
  simp only [arithmeticSum, reducedResidues, reducedFrequencySum, frequencyWeight,
    Nat.cast_mul, Nat.cast_ofNat]

theorem odd_reduced_reference_frequency {k : ℕ} (hk : 0 < k) (hkOdd : Odd k) (n : ℕ) :
    fourierCoefficient reducedResidues k n = -prefactor k *
      ((coefficient k 0 : ℂ) * (starRingEnd ℂ) (referenceSum (2*k) (-(n : ℝ)))) := by
  rw [actual_reduced_fourier_reference hk]
  simp [shiftedFrequency, hkOdd.neg_one_pow]

theorem even_reduced_reference_frequency {k : ℕ} (hk : 0 < k) (hkEven : Even k) (n : ℕ) :
    fourierCoefficient reducedResidues k n = -prefactor k *
      ((coefficient k 0 : ℂ) *
        (starRingEnd ℂ) (referenceSum (2*k) (-(n : ℝ) - (k : ℝ)/2))) := by
  have h : shiftedFrequency k n = -(n : ℝ) - (k : ℝ)/2 := by
    rw [shiftedFrequency, hkEven.neg_one_pow]
    ring
  rw [actual_reduced_fourier_reference hk, h]

end
end ManuscriptAudit.Paper8DedekindReferenceFrequency

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DedekindReferenceFrequency.referenceSum_at_zero,
      ``ManuscriptAudit.Paper8DedekindReferenceFrequency.reducedFrequencySum_eq_conj_reference,
      ``ManuscriptAudit.Paper8DedekindReferenceFrequency.actual_reduced_fourier_reference,
      ``ManuscriptAudit.Paper8DedekindReferenceFrequency.odd_reduced_reference_frequency,
      ``ManuscriptAudit.Paper8DedekindReferenceFrequency.even_reduced_reference_frequency] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
