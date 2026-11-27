import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Rat.Floor
import PrimalitySheafVerification.ManuscriptAudit.Paper8HolomorphicPartPhase

/-!
# The actual first-coefficient residue weights in physical p. 335

The printed display only says d modulo 2k. Rhoades' primary proof
https://arxiv.org/pdf/1111.1495, §2, uses relatively prime residues
in the Kloosterman-like sum. Both readings are defined with the literal
Dedekind sawtooth. The k=1 signed weight is 1 for the reduced reading
and 0 for the all-residue reading.
-/

namespace ManuscriptAudit.Paper8ContourResidueWeights

open Paper8HolomorphicPartPhase (periodCoefficient)

noncomputable section

def sawtooth (x : ℚ) : ℚ :=
  if x = (⌊x⌋ : ℚ) then 0 else x - (⌊x⌋ : ℚ) - 1 / 2

def dedekindSum (h : ℤ) (n : ℕ) : ℚ :=
  ∑ j : Fin n, sawtooth ((j.val : ℚ) / (n : ℚ)) *
    sawtooth ((h : ℚ) * (j.val : ℚ) / (n : ℚ))

def firstPhase (k : ℕ) (d : Fin (2 * k)) : ℝ :=
  (dedekindSum (-(d.val : ℤ)) (2 * k) : ℝ) / 2 -
    (d.val : ℝ) / 8 * (1 + (-1 : ℝ) ^ k) + (d.val : ℝ) / (2 * (k : ℝ))

def residueWeight (k : ℕ) (d : Fin (2 * k)) : ℂ :=
  Complex.exp (periodCoefficient * (firstPhase k d : ℂ))

def prefactor (k : ℕ) : ℂ := (-1 : ℂ) ^ ((k + 1) / 2) / (k : ℂ)

def weighted (k : ℕ) (S : Finset (Fin (2 * k))) : ℂ :=
  prefactor k * ∑ d ∈ S, residueWeight k d

def reducedResidues (k : ℕ) : Finset (Fin (2 * k)) :=
  Finset.univ.filter (fun d => Nat.Coprime d.val (2 * k))

def reducedWeight (k : ℕ) : ℂ := weighted k (reducedResidues k)

def allWeight (k : ℕ) : ℂ := weighted k Finset.univ

theorem residueWeight_norm (k : ℕ) (d : Fin (2 * k)) : ‖residueWeight k d‖ = 1 := by
  rw [residueWeight, Complex.norm_exp]
  simp [periodCoefficient, Complex.mul_re, Complex.mul_im]

theorem weighted_norm_le_two {k : ℕ} (hk : 0 < k) (S : Finset (Fin (2 * k))) :
    ‖weighted k S‖ ≤ 2 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkC : ‖(k : ℂ)‖ = (k : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hCard : (S.card : ℝ) ≤ 2 * (k : ℝ) := by
    have h : S.card ≤ 2 * k := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    exact_mod_cast h
  have hSum : ‖∑ d ∈ S, residueWeight k d‖ ≤ (S.card : ℝ) := by
    calc
      _ ≤ ∑ d ∈ S, ‖residueWeight k d‖ := norm_sum_le _ _
      _ = _ := by simp [residueWeight_norm]
  rw [weighted, norm_mul, prefactor, norm_div, norm_pow, norm_neg, norm_one, one_pow, hkC]
  calc
    _ ≤ (1 / (k : ℝ)) * (2 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (hSum.trans hCard) (by positivity)
    _ = _ := by field_simp [hkR.ne']

private theorem residue_one_zero : residueWeight 1 (0 : Fin 2) = 1 := by
  have h : dedekindSum 0 2 = 0 := by
    norm_num [dedekindSum, Fin.sum_univ_two, sawtooth]
  simp [residueWeight, firstPhase, h]

private theorem residue_one_one : residueWeight 1 (1 : Fin 2) = -1 := by
  have h : dedekindSum (-1) 2 = 0 := by
    norm_num [dedekindSum, Fin.sum_univ_two, sawtooth]
  have hp : firstPhase 1 (1 : Fin 2) = 1 / 2 := by
    norm_num [firstPhase, h]
  rw [residueWeight, hp]
  have he : periodCoefficient * ((1 / 2 : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
    rw [periodCoefficient, Complex.ofReal_div]
    simp only [Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he, Complex.exp_pi_mul_I]

theorem reducedWeight_one : reducedWeight 1 = 1 := by
  have hS : reducedResidues 1 = ({1} : Finset (Fin 2)) := by decide
  rw [reducedWeight, weighted, hS, Finset.sum_singleton, residue_one_one]
  norm_num [prefactor]

theorem allWeight_one : allWeight 1 = 0 := by
  change prefactor 1 * (∑ d : Fin 2, residueWeight 1 d) = 0
  rw [Fin.sum_univ_two, residue_one_zero, residue_one_one]
  norm_num

private theorem firstPhase_two_zero : firstPhase 2 (0 : Fin 4) = 0 := by
  have h : dedekindSum 0 4 = 0 := by
    norm_num [dedekindSum, Fin.sum_univ_four, sawtooth]
  norm_num [firstPhase, h]

private theorem firstPhase_two_one : firstPhase 2 (1 : Fin 4) = -1 / 16 := by
  have h : dedekindSum (-1) 4 = -1 / 8 := by
    norm_num [dedekindSum, Fin.sum_univ_four, sawtooth]
  norm_num [firstPhase, h]

private theorem firstPhase_two_two : firstPhase 2 (2 : Fin 4) = 0 := by
  have h : dedekindSum (-2) 4 = 0 := by
    norm_num [dedekindSum, Fin.sum_univ_four, sawtooth]
  norm_num [firstPhase, h]

private theorem firstPhase_two_three : firstPhase 2 (3 : Fin 4) = 1 / 16 := by
  have h : dedekindSum (-3) 4 = 1 / 8 := by
    norm_num [dedekindSum, Fin.sum_univ_four, sawtooth]
  norm_num [firstPhase, h]

private theorem residueWeight_re_eq_cos (k : ℕ) (d : Fin (2 * k)) :
    (residueWeight k d).re = Real.cos (2 * Real.pi * firstPhase k d) := by
  have h : periodCoefficient * (firstPhase k d : ℂ) =
      ((2 * Real.pi * firstPhase k d : ℝ) : ℂ) * Complex.I := by
    rw [periodCoefficient]
    push_cast
    ring
  rw [residueWeight, h, Complex.exp_ofReal_mul_I_re]

theorem allWeight_two_re :
    (allWeight 2).re = -(1 + Real.cos (Real.pi / 8)) := by
  have hPref : prefactor 2 = ((-(1 / 2 : ℝ)) : ℂ) := by
    norm_num [prefactor, Complex.ofReal_div]
  change (prefactor 2 * (∑ d : Fin 4, residueWeight 2 d)).re = _
  rw [hPref, Fin.sum_univ_four, Complex.mul_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero,
    zero_mul, sub_zero, Complex.add_re,
    residueWeight_re_eq_cos, firstPhase_two_zero, firstPhase_two_one, firstPhase_two_two,
    firstPhase_two_three, mul_zero, Real.cos_zero]
  rw [show 2 * Real.pi * (-1 / 16 : ℝ) = -(Real.pi / 8) by ring,
    show 2 * Real.pi * (1 / 16 : ℝ) = Real.pi / 8 by ring, Real.cos_neg]
  ring

end
end ManuscriptAudit.Paper8ContourResidueWeights

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourResidueWeights.residueWeight_norm,
      ``ManuscriptAudit.Paper8ContourResidueWeights.weighted_norm_le_two,
      ``ManuscriptAudit.Paper8ContourResidueWeights.reducedWeight_one,
      ``ManuscriptAudit.Paper8ContourResidueWeights.allWeight_one,
      ``ManuscriptAudit.Paper8ContourResidueWeights.allWeight_two_re] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
