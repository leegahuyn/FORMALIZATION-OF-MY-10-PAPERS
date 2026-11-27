import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.SumPrimeReciprocals
import PrimalitySheafVerification.ManuscriptAudit.Paper8LiteralLowerAbsolute

/-!
# Termwise absolute summation also fails for reduced residues

For prime rows k = p there are φ(2p) ≥ p/2 reduced residues.
The common reflected coefficient still forces divergence of the
sum of row norm masses on this prime subsequence.
-/

namespace ManuscriptAudit.Paper8ReducedLowerAbsolute

open Paper8ContourGammaSeries (coefficient coefficient_pos)
open Paper8ContourResidueWeights (prefactor residueWeight residueWeight_norm reducedResidues)
open Paper8LocalContour (phi)
open Paper8HolomorphicPartPhase (qParameter)
open Paper8FixedContourSingle (common singleRemainder)
open Paper8FixedContourDifference (phiAtQ)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos)
open Paper8ContourGammaRemainder (bound bound_nonneg)
open Paper8ContourSignedDominance (decay decay_nonneg decay_tail_summable)
open Paper8ReflectedContourSingle (phi_eq_common_add_remainder singleRemainder_norm_le)
open Paper8LowerContourParameterLink (nome_mul_phi_eq_inverse_nome)
open Paper8OddGcdOrderedLimit (coefficient_zero_rescale)
open Paper8LiteralLowerAbsolute (inverseRoot inverseRoot_norm common_norm_ge)

noncomputable section

theorem reduced_card_eq_totient (k : ℕ) :
    (reducedResidues k).card = (2 * k).totient := by
  unfold reducedResidues
  rw [Nat.totient_eq_card_coprime]
  refine Finset.card_bij (fun (d : Fin (2 * k)) _ => d.val) ?_ ?_ ?_
  · intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr d.isLt, (Finset.mem_filter.mp hd).2.symm⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro d hd
    obtain ⟨hr, hc⟩ := Finset.mem_filter.mp hd
    exact ⟨⟨d, Finset.mem_range.mp hr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.symm⟩, rfl⟩

theorem prime_reduced_card_leading {p : ℕ} (hp : p.Prime) :
    p ≤ 2 * (reducedResidues p).card := by
  rw [reduced_card_eq_totient]
  rcases hp.eq_two_or_odd' with rfl | ho
  · decide
  · rw [Nat.totient_two_mul_of_odd ho, Nat.totient_prime hp]
    have h := hp.two_le
    omega

private theorem prime_coefficients_not_summable :
    ¬ Summable (fun p : Nat.Primes => coefficient p.val 0) := by
  intro h
  have hC := (coefficient_pos (Nat.succ_pos 0) 0).ne'
  have hP : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
    apply (h.mul_right (coefficient 1 0)⁻¹).congr
    intro p
    have hh := coefficient_zero_rescale p.prop.pos (Nat.succ_pos 0)
    rw [Nat.mul_one] at hh
    rw [hh, mul_assoc, mul_inv_cancel₀ hC, mul_one,
      Real.rpow_neg (Nat.cast_nonneg p.val), one_div]
  have hp := Nat.Primes.summable_rpow.mp hP
  norm_num at hp

def inverseNomeMass (α β : ℝ) (Q : ℂ) (k : ℕ) : ℝ :=
  (∑ d ∈ reducedResidues k, ‖phiAtQ (-α) (-β) k (inverseRoot k d) Q‖) / (k : ℝ)

theorem inverse_nome_reduced_mass_not_summable {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) {Q : ℂ} (hQ : ‖Q‖ ≤ 1 / 4) :
    ¬ Summable (fun j : ℕ => inverseNomeMass α β Q (j + 1)) := by
  intro hS
  let C := 4 * fixedRadius * bound fixedRadius
  have hC : 0 ≤ C := by
    unfold C
    exact mul_nonneg (mul_nonneg (by norm_num) fixedRadius_pos.le) (bound_nonneg fixedRadius_pos)
  have hT : Summable (fun k : ℕ => decay k) := by
    exact (summable_nat_add_iff 2).1 (decay_tail_summable 2 (by decide))
  have h : Summable (fun p : Nat.Primes => inverseNomeMass α β Q p.val) :=
    ((summable_nat_add_iff 1).1 hS).subtype _
  have hTail : Summable (fun p : Nat.Primes => 2 * (C * decay p.val)) :=
    ((hT.mul_left C).mul_left 2).subtype _
  apply prime_coefficients_not_summable
  refine Summable.of_nonneg_of_le (fun p => (coefficient_pos p.prop.pos 0).le) ?_
    ((h.add hTail).mul_left (5 / 2 : ℝ))
  intro p
  let k := p.val
  have hk : 0 < k := p.prop.pos
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let s := reducedResidues k
  let b := (4 / 5 : ℝ) * coefficient k 0
  have hb : 0 ≤ b := mul_nonneg (by norm_num) (coefficient_pos hk 0).le
  have hPoint (d : Fin (2 * k)) :
      b ≤ ‖phiAtQ (-α) (-β) k (inverseRoot k d) Q‖ + C * decay k := by
    let ζ := inverseRoot k d
    have hEq := phi_eq_common_add_remainder α hβ hβ' hk (inverseRoot_norm k d) hQ
    calc
      _ ≤ ‖common k ζ Q‖ := common_norm_ge hk (inverseRoot_norm k d) hQ
      _ = ‖phiAtQ (-α) (-β) k ζ Q - singleRemainder (-α) (-β) k ζ Q‖ := by
        rw [hEq, add_sub_cancel_right]
      _ ≤ ‖phiAtQ (-α) (-β) k ζ Q‖ + ‖singleRemainder (-α) (-β) k ζ Q‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add_left
        (singleRemainder_norm_le hα hα' hβ hβ' hk (inverseRoot_norm k d) hQ) _
  have hRow := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun d (_ : d ∈ s) => hPoint d)) hkR.le
  rw [Finset.sum_add_distrib, add_div] at hRow
  simp only [Finset.sum_const, nsmul_eq_mul] at hRow
  have hLowerNat : k ≤ 2 * s.card := prime_reduced_card_leading p.prop
  have hUpperNat : s.card ≤ 2 * k := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ s)
  have hLower : (1 / 2 : ℝ) ≤ (s.card : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hkR]
    have hh : (k : ℝ) ≤ 2 * (s.card : ℝ) := by exact_mod_cast hLowerNat
    linarith
  have hUpper : (s.card : ℝ) / (k : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hkR]
    exact_mod_cast hUpperNat
  have hbL : (1 / 2 : ℝ) * b ≤ (s.card : ℝ) * b / (k : ℝ) := by
    calc
      _ ≤ ((s.card : ℝ) / (k : ℝ)) * b := mul_le_mul_of_nonneg_right hLower hb
      _ = _ := div_mul_eq_mul_div _ _ _
  have hcU : (s.card : ℝ) * (C * decay k) / (k : ℝ) ≤ 2 * (C * decay k) := by
    calc
      _ = ((s.card : ℝ) / (k : ℝ)) * (C * decay k) := (div_mul_eq_mul_div _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hUpper (mul_nonneg hC (decay_nonneg k))
  change (s.card : ℝ) * b / (k : ℝ) ≤ inverseNomeMass α β Q k +
    (s.card : ℝ) * (C * decay k) / (k : ℝ) at hRow
  have h : (1 / 2 : ℝ) * b ≤ inverseNomeMass α β Q k + 2 * (C * decay k) :=
    hbL.trans (hRow.trans (add_le_add_left hcU _))
  unfold b at h
  exact (show coefficient k 0 ≤ (5 / 2 : ℝ) *
    (inverseNomeMass α β Q k + 2 * (C * decay k)) by linarith only [h])

theorem reduced_lower_residue_norms_not_summable {z : ℂ} (hz : z.im < 0)
    (hQ : ‖qParameter (-z)‖ ≤ 1 / 4) :
    ¬ Summable (fun j : ℕ => ∑ d ∈ reducedResidues (j + 1),
      ‖prefactor (j + 1) * residueWeight (j + 1) d *
        (qParameter z * phi (2 / 3) 16 (j + 1) (d.val : ℤ) z)‖) := by
  intro h
  apply inverse_nome_reduced_mass_not_summable (α := (16 - 2 / 3 : ℝ)) (β := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hQ
  apply h.congr
  intro j
  let k := j + 1
  have hk : 0 < k := Nat.succ_pos j
  have hCast : ‖(k : ℂ)‖ = (k : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg k)]
  have hPrefactor : ‖prefactor k‖ = 1 / (k : ℝ) := by
    rw [prefactor, norm_div, norm_pow, norm_neg, norm_one, one_pow, hCast]
  have hAlpha : (2 / 3 : ℝ) - 16 = -(16 - 2 / 3 : ℝ) := by ring
  unfold inverseNomeMass
  rw [div_eq_inv_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  change ‖prefactor k * residueWeight k d * (qParameter z * phi (2 / 3) 16 k (d.val : ℤ) z)‖ =
    (k : ℝ)⁻¹ * ‖phiAtQ (-(16 - 2 / 3 : ℝ)) (-16) k (inverseRoot k d) (qParameter (-z))‖
  rw [nome_mul_phi_eq_inverse_nome (2 / 3) (by norm_num : (0 : ℝ) < 16) (by norm_num)
    hk (d.val : ℤ) hz hQ, hAlpha]
  change ‖prefactor k * residueWeight k d *
    (-inverseRoot k d * phiAtQ (-(16 - 2 / 3 : ℝ)) (-16) k (inverseRoot k d) (qParameter (-z)))‖ = _
  simp only [norm_mul, hPrefactor, residueWeight_norm, norm_neg, inverseRoot_norm, mul_one,
    one_mul, one_div]

end
end ManuscriptAudit.Paper8ReducedLowerAbsolute

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReducedLowerAbsolute.reduced_card_eq_totient,
      ``ManuscriptAudit.Paper8ReducedLowerAbsolute.prime_reduced_card_leading,
      ``ManuscriptAudit.Paper8ReducedLowerAbsolute.inverse_nome_reduced_mass_not_summable,
      ``ManuscriptAudit.Paper8ReducedLowerAbsolute.reduced_lower_residue_norms_not_summable] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
