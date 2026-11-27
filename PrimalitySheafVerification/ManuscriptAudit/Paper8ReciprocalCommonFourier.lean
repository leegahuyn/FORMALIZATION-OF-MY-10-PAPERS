import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecificLimits.Normed
import PrimalitySheafVerification.ManuscriptAudit.Paper8SeparateReciprocalContourSeries

/-!
# Native finite-modulus Fourier expansion for the shared reciprocal term

For a fixed modulus the finite residue sum may be expanded as a
geometric series in Q. The same holds for every finite modulus
partial sum. No interchange of two infinite sums occurs here.
-/

namespace ManuscriptAudit.Paper8ReciprocalCommonFourier

open Paper8LocalContour (root)
open Paper8ContourResidueWeights (prefactor residueWeight)
open Paper8ContourGammaSeries (coefficient)
open Paper8ContourDifferenceTerms (root_power_norm)
open Paper8FixedContourSingle (common)
open Paper8SeparateReciprocalContourSeries (commonTerm sumKernel)
open Paper8SeparateContourSeries (orderedPartialSum)

noncomputable section

def fourierCoefficient (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k n : ℕ) : ℂ :=
  -prefactor k * ∑ d ∈ S k, residueWeight k d *
    ((root k ^ (d.val : ℤ))⁻¹ * (coefficient k 0 : ℂ) * ((root k ^ (d.val : ℤ))⁻¹) ^ n)

theorem row_hasSum (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) {Q : ℂ}
    (hQ : ‖Q‖ < 1) :
    HasSum (fun n : ℕ => fourierCoefficient S k n * Q ^ n) (commonTerm S k Q) := by
  let ζ (d : Fin (2 * k)) := (root k ^ (d.val : ℤ))⁻¹
  let A (d : Fin (2 * k)) := residueWeight k d * (ζ d * (coefficient k 0 : ℂ))
  have hGeo (d : Fin (2 * k)) :
      HasSum (fun n : ℕ => A d * (ζ d * Q) ^ n) (A d * (1 - ζ d * Q)⁻¹) := by
    have hNorm : ‖ζ d * Q‖ < 1 := by
      change ‖(root k ^ (d.val : ℤ))⁻¹ * Q‖ < 1
      rwa [norm_mul, norm_inv, root_power_norm k d, inv_one, one_mul]
    exact (hasSum_geometric_of_norm_lt_one hNorm).mul_left (A d)
  have hSum : HasSum (fun n : ℕ => ∑ d ∈ S k, A d * (ζ d * Q) ^ n)
      (∑ d ∈ S k, A d * (1 - ζ d * Q)⁻¹) := hasSum_sum (fun d _ => hGeo d)
  have hF : (fun n : ℕ => -prefactor k * ∑ d ∈ S k, A d * (ζ d * Q) ^ n) =
      (fun n : ℕ => fourierCoefficient S k n * Q ^ n) := by
    funext n
    unfold fourierCoefficient
    rw [mul_assoc (-prefactor k), Finset.sum_mul]
    apply congrArg (fun w : ℂ => -prefactor k * w)
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_pow]
    unfold A ζ
    ring
  have hVal : -prefactor k * (∑ d ∈ S k, A d * (1 - ζ d * Q)⁻¹) = commonTerm S k Q := by
    unfold commonTerm sumKernel common
    apply congrArg (fun w : ℂ => -prefactor k * w)
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [A, ζ, div_eq_mul_inv, mul_assoc]
  have h := hSum.mul_left (-prefactor k)
  change HasSum (fun n : ℕ => -prefactor k * ∑ d ∈ S k, A d * (ζ d * Q) ^ n)
    (-prefactor k * ∑ d ∈ S k, A d * (1 - ζ d * Q)⁻¹) at h
  rw [hF, hVal] at h
  exact h

def orderedFourierCoefficient (S : ∀ k : ℕ, Finset (Fin (2 * k))) (N n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, fourierCoefficient S (k + 1) n

theorem finite_modulus_sum_hasSum (S : ∀ k : ℕ, Finset (Fin (2 * k))) (N : ℕ) {Q : ℂ}
    (hQ : ‖Q‖ < 1) :
    HasSum (fun n : ℕ => orderedFourierCoefficient S N n * Q ^ n)
      (orderedPartialSum (fun k => commonTerm S (k + 1) Q) N) := by
  have h : HasSum (fun n : ℕ => ∑ k ∈ Finset.range N, fourierCoefficient S (k + 1) n * Q ^ n)
      (∑ k ∈ Finset.range N, commonTerm S (k + 1) Q) :=
    hasSum_sum (fun k _ => row_hasSum S (k + 1) hQ)
  exact h.congr_fun fun n => by rw [orderedFourierCoefficient, Finset.sum_mul]

end
end ManuscriptAudit.Paper8ReciprocalCommonFourier

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReciprocalCommonFourier.row_hasSum,
      ``ManuscriptAudit.Paper8ReciprocalCommonFourier.finite_modulus_sum_hasSum] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
