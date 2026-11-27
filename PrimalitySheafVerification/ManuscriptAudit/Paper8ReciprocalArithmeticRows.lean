import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalCommonFourier

/-!
# Exact arithmetic normalization of the reciprocal Fourier rows

For reduced residues, the finite root-of-unity sum below is the
Dedekind sum A_{2k} with the shifted negative frequency used in
Rhoades §3 and Bringmann–Ono (4.3). This is a finite identity.
-/

namespace ManuscriptAudit.Paper8ReciprocalArithmeticRows

open Paper8LocalContour (root root_eq_literal)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8ContourResidueWeights (dedekindSum firstPhase residueWeight prefactor)
open Paper8ContourGammaSeries (coefficient)
open Paper8ReciprocalCommonFourier (fourierCoefficient)

noncomputable section

def shiftedFrequency (k n : ℕ) : ℝ :=
  -(n : ℝ) - (k : ℝ) * (1 + (-1 : ℝ) ^ k) / 4

def arithmeticSum (S : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (u : ℝ) : ℂ :=
  ∑ d ∈ S k, Complex.exp (periodCoefficient *
    ((dedekindSum (-(d.val : ℤ)) (2 * k) : ℝ) / 2 + u * (d.val : ℝ) / (2 * (k : ℝ)) : ℝ))

theorem shiftedFrequency_integral (k n : ℕ) :
    ∃ u : ℤ, (u : ℝ) = shiftedFrequency k n := by
  rcases Nat.even_or_odd k with h | h
  · have hp : (-1 : ℝ) ^ k = 1 := h.neg_one_pow
    obtain ⟨m, hm⟩ := h
    refine ⟨-(n : ℤ) - (m : ℤ), ?_⟩
    rw [shiftedFrequency, hp, hm]
    push_cast
    ring
  · have hp : (-1 : ℝ) ^ k = -1 := h.neg_one_pow
    refine ⟨-(n : ℤ), ?_⟩
    norm_num [shiftedFrequency, hp]

private theorem reciprocal_root_exp {k : ℕ} (hk : 0 < k) (d : Fin (2 * k)) :
    (root k ^ (d.val : ℤ))⁻¹ =
      Complex.exp (periodCoefficient * ((-(d.val : ℝ) / (2 * (k : ℝ)) : ℝ) : ℂ)) := by
  rw [root_eq_literal hk, ← Complex.exp_int_mul, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

private theorem residue_mode_exp {k : ℕ} (hk : 0 < k) (n : ℕ) (d : Fin (2 * k)) :
    residueWeight k d * (root k ^ (d.val : ℤ))⁻¹ * ((root k ^ (d.val : ℤ))⁻¹) ^ n =
      Complex.exp (periodCoefficient *
        ((dedekindSum (-(d.val : ℤ)) (2 * k) : ℝ) / 2 +
          shiftedFrequency k n * (d.val : ℝ) / (2 * (k : ℝ)) : ℝ)) := by
  let x : ℝ := -(d.val : ℝ) / (2 * (k : ℝ))
  have hx : (root k ^ (d.val : ℤ))⁻¹ = Complex.exp (periodCoefficient * (x : ℂ)) :=
    reciprocal_root_exp hk d
  have hK : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hPhase : firstPhase k d + x + (n : ℝ) * x =
      (dedekindSum (-(d.val : ℤ)) (2 * k) : ℝ) / 2 +
        shiftedFrequency k n * (d.val : ℝ) / (2 * (k : ℝ)) := by
    unfold firstPhase shiftedFrequency x
    field_simp [hK.ne'] <;> ring
  rw [residueWeight, hx, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add,
    ← hPhase]
  congr 1
  push_cast
  ring

theorem fourierCoefficient_eq_arithmeticSum (S : ∀ k : ℕ, Finset (Fin (2 * k)))
    {k : ℕ} (hk : 0 < k) (n : ℕ) :
    fourierCoefficient S k n = -prefactor k *
      ((coefficient k 0 : ℂ) * arithmeticSum S k (shiftedFrequency k n)) := by
  let E (d : Fin (2 * k)) := Complex.exp (periodCoefficient *
    ((dedekindSum (-(d.val : ℤ)) (2 * k) : ℝ) / 2 +
      shiftedFrequency k n * (d.val : ℝ) / (2 * (k : ℝ)) : ℝ))
  have hMul : (coefficient k 0 : ℂ) * (∑ d ∈ S k, E d) =
      ∑ d ∈ S k, (coefficient k 0 : ℂ) * E d := by rw [Finset.mul_sum]
  change fourierCoefficient S k n = -prefactor k * ((coefficient k 0 : ℂ) * (∑ d ∈ S k, E d))
  rw [fourierCoefficient, hMul]
  apply congrArg (fun w : ℂ => -prefactor k * w)
  refine Finset.sum_congr rfl fun d _ => ?_
  change _ = (coefficient k 0 : ℂ) * E d
  unfold E
  rw [← residue_mode_exp hk n d]
  ring

end
end ManuscriptAudit.Paper8ReciprocalArithmeticRows

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReciprocalArithmeticRows.shiftedFrequency_integral,
      ``ManuscriptAudit.Paper8ReciprocalArithmeticRows.fourierCoefficient_eq_arithmeticSum] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
