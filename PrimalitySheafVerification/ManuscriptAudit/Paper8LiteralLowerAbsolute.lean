import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8LowerContourParameterLink
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdOrderedLimit

/-!
# The literal lower contour cannot be summed absolutely before the residue sum

Every residue contributes a leading term of order k^(-3/2) to
the norm sum with the printed prefactor. There are 2k residues.
The remaining reflected-kernel norm sum is summable. This concerns
absolute summation over residues and moduli and leaves the ordinary
sum after combination of the residues to the arithmetic analysis.
-/

namespace ManuscriptAudit.Paper8LiteralLowerAbsolute

open Paper8ContourGammaSeries (coefficient coefficient_pos)
open Paper8ContourResidueWeights (prefactor residueWeight residueWeight_norm)
open Paper8LocalContour (phi root)
open Paper8ContourDifferenceTerms (root_power_norm)
open Paper8HolomorphicPartPhase (qParameter)
open Paper8FixedContourSingle (common singleRemainder)
open Paper8FixedContourDifference (phiAtQ)
open Paper8FixedContourParameter (fixedRadius fixedRadius_pos)
open Paper8ContourGammaRemainder (bound)
open Paper8ContourSignedDominance (decay decay_tail_summable)
open Paper8ReflectedContourSingle (phi_eq_common_add_remainder singleRemainder_norm_le)
open Paper8LowerContourParameterLink (nome_mul_phi_eq_inverse_nome)
open Paper8OddGcdOrderedLimit (coefficient_zero_rescale)

noncomputable section

def inverseRoot (k : ℕ) (d : Fin (2 * k)) : ℂ := (root k ^ (d.val : ℤ))⁻¹

theorem inverseRoot_norm (k : ℕ) (d : Fin (2 * k)) : ‖inverseRoot k d‖ = 1 := by
  rw [inverseRoot, norm_inv, root_power_norm, inv_one]

def rowNorm (k : ℕ) (F : Fin (2 * k) → ℂ) : ℝ :=
  (∑ d : Fin (2 * k), ‖F d‖) / (k : ℝ)

private theorem rowNorm_constant {k : ℕ} (hk : 0 < k) (c : ℝ) :
    (∑ _ : Fin (2 * k), c) / (k : ℝ) = 2 * c := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
    Nat.cast_ofNat]
  field_simp [hkR] <;> ring

theorem common_norm_ge {k : ℕ} (hk : 0 < k) {ζ Q : ℂ}
    (hζ : ‖ζ‖ = 1) (hQ : ‖Q‖ ≤ 1 / 4) :
    (4 / 5 : ℝ) * coefficient k 0 ≤ ‖common k ζ Q‖ := by
  have hc := (coefficient_pos hk 0).le
  have hN : ‖ζ * Q‖ = ‖Q‖ := by rw [norm_mul, hζ, one_mul]
  have hNe : (1 : ℂ) - ζ * Q ≠ 0 := by
    intro h
    have hOne := congrArg (fun z : ℂ => ‖z‖) (sub_eq_zero.mp h)
    rw [norm_one, hN] at hOne
    linarith
  have hDiv : 0 < ‖(1 : ℂ) - ζ * Q‖ := norm_pos_iff.mpr hNe
  have hBound : ‖(1 : ℂ) - ζ * Q‖ ≤ (5 / 4 : ℝ) := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖ζ * Q‖ := norm_sub_le _ _
      _ = 1 + ‖Q‖ := by rw [norm_one, hN]
      _ ≤ _ := by linarith
  rw [common, norm_div, Complex.norm_real, Real.norm_of_nonneg hc, le_div_iff₀ hDiv]
  calc
    _ ≤ ((4 / 5 : ℝ) * coefficient k 0) * (5 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hBound (mul_nonneg (by norm_num) hc)
    _ = _ := by ring

theorem reflected_kernel_norm_lower {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) {k : ℕ} (hk : 0 < k) {ζ Q : ℂ}
    (hζ : ‖ζ‖ = 1) (hQ : ‖Q‖ ≤ 1 / 4) :
    (4 / 5 : ℝ) * coefficient k 0 ≤ ‖phiAtQ (-α) (-β) k ζ Q‖ +
      (4 * fixedRadius * bound fixedRadius) * decay k := by
  have hEq : phiAtQ (-α) (-β) k ζ Q = common k ζ Q + singleRemainder (-α) (-β) k ζ Q :=
    phi_eq_common_add_remainder α hβ hβ' hk hζ hQ
  have hRem : ‖singleRemainder (-α) (-β) k ζ Q‖ ≤ (4 * fixedRadius * bound fixedRadius) * decay k :=
    singleRemainder_norm_le hα hα' hβ hβ' hk hζ hQ
  calc
    _ ≤ ‖common k ζ Q‖ := common_norm_ge hk hζ hQ
    _ = ‖phiAtQ (-α) (-β) k ζ Q - singleRemainder (-α) (-β) k ζ Q‖ := by
      rw [hEq, add_sub_cancel_right]
    _ ≤ ‖phiAtQ (-α) (-β) k ζ Q‖ + ‖singleRemainder (-α) (-β) k ζ Q‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add_left hRem ‖phiAtQ (-α) (-β) k ζ Q‖

private theorem coefficient_not_summable : ¬ Summable (fun j : ℕ => coefficient (j + 1) 0) := by
  intro h
  have hC := (coefficient_pos (Nat.succ_pos 0) 0).ne'
  have hP : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
    apply (h.mul_right (coefficient 1 0)⁻¹).congr
    intro j
    have hh := coefficient_zero_rescale (Nat.succ_pos j) (Nat.succ_pos 0)
    rw [Nat.mul_one] at hh
    rw [hh, mul_assoc, mul_inv_cancel₀ hC, mul_one]
  have hp := Real.summable_one_div_nat_rpow.1 ((summable_nat_add_iff 1).1 hP)
  norm_num at hp

set_option maxHeartbeats 800000 in
theorem inverse_nome_row_norm_not_summable {α β : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 24)
    (hβ : 0 ≤ β) (hβ' : β ≤ 24) {Q : ℂ} (hQ : ‖Q‖ ≤ 1 / 4) :
    ¬ Summable (fun j : ℕ => rowNorm (j + 1)
      (fun d => phiAtQ (-α) (-β) (j + 1) (inverseRoot (j + 1) d) Q)) := by
  intro hSum
  let C := (4 * fixedRadius * bound fixedRadius)
  have hTail : Summable (fun j : ℕ => 2 * (C * decay (j + 1))) := by
    have hd : Summable (fun j : ℕ => decay (j + 1)) :=
      (summable_nat_add_iff 1).1 (decay_tail_summable 2 (by decide))
    exact (hd.mul_left C).mul_left 2
  apply coefficient_not_summable
  refine Summable.of_nonneg_of_le (fun j => (coefficient_pos (Nat.succ_pos j) 0).le) ?_
    (((hSum.add hTail).mul_left (5 / 8 : ℝ)))
  intro j
  let k := j + 1
  have hk : 0 < k := Nat.succ_pos j
  have hPoint (d : Fin (2 * k)) :
      (4 / 5 : ℝ) * coefficient k 0 ≤
        ‖phiAtQ (-α) (-β) k (inverseRoot k d) Q‖ + C * decay k :=
    reflected_kernel_norm_lower hα hα' hβ hβ' hk (inverseRoot_norm k d) hQ
  have hRow := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => hPoint d)) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  rw [rowNorm_constant hk, Finset.sum_add_distrib, add_div, rowNorm_constant hk] at hRow
  change coefficient k 0 ≤ (5 / 8 : ℝ) *
    (rowNorm k (fun d => phiAtQ (-α) (-β) k (inverseRoot k d) Q) + 2 * (C * decay k))
  change 2 * ((4 / 5 : ℝ) * coefficient k 0) ≤
    rowNorm k (fun d => phiAtQ (-α) (-β) k (inverseRoot k d) Q) + 2 * (C * decay k) at hRow
  linarith only [hRow]

theorem literal_lower_residue_norms_not_summable {z : ℂ} (hz : z.im < 0)
    (hQ : ‖qParameter (-z)‖ ≤ 1 / 4) :
    ¬ Summable (fun j : ℕ => ∑ d : Fin (2 * (j + 1)),
      ‖prefactor (j + 1) * residueWeight (j + 1) d *
        (qParameter z * phi (2 / 3) 16 (j + 1) (d.val : ℤ) z)‖) := by
  intro h
  apply inverse_nome_row_norm_not_summable (α := (16 - 2 / 3 : ℝ)) (β := 16)
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
  unfold rowNorm
  conv_rhs => rw [div_eq_inv_mul, Finset.mul_sum]
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
end ManuscriptAudit.Paper8LiteralLowerAbsolute

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8LiteralLowerAbsolute.inverse_nome_row_norm_not_summable,
      ``ManuscriptAudit.Paper8LiteralLowerAbsolute.literal_lower_residue_norms_not_summable] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
