import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FixedContourDifferenceBounds
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourResidueWeights

/-! Actual residue-weighted terms of the fixed-radius contour difference. -/

namespace ManuscriptAudit.Paper8ContourDifferenceTerms

open Paper8ContourResidueWeights (prefactor residueWeight residueWeight_norm weighted)
open Paper8LocalContour (root root_norm)
open Paper8FixedContourDifference (difference difference_at_zero)
open Paper8FixedContourDifferenceBounds (difference_norm_le difference_sub_zero_norm_le)
open Paper8FixedContourParameter (fixedRadius)
open Paper8ContourGammaRemainder (bound)
open Paper8ContourSignedDominance (decay)
open Paper8ContourCoefficientDecay (delta)

noncomputable section

def term (residues : ∀ k : ℕ, Finset (Fin (2 * k))) (k : ℕ) (q : ℂ) : ℂ :=
  prefactor k * ∑ d ∈ residues k, residueWeight k d * difference k (root k ^ (d.val : ℤ)) q

theorem root_power_norm (k : ℕ) (d : Fin (2 * k)) : ‖root k ^ (d.val : ℤ)‖ = 1 := by
  rw [norm_zpow, root_norm, one_zpow]

theorem norm_weighted_le {k : ℕ} (hk : 0 < k) (S : Finset (Fin (2 * k)))
    (f : Fin (2 * k) → ℂ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ d ∈ S, ‖f d‖ ≤ c) :
    ‖prefactor k * ∑ d ∈ S, residueWeight k d * f d‖ ≤ 2 * c := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkC : ‖(k : ℂ)‖ = (k : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hCard : (S.card : ℝ) ≤ 2 * (k : ℝ) := by
    have ht : S.card ≤ 2 * k := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    exact_mod_cast ht
  have hSum : ‖∑ d ∈ S, residueWeight k d * f d‖ ≤ (2 * (k : ℝ)) * c := by
    calc
      _ ≤ ∑ d ∈ S, ‖residueWeight k d * f d‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ S, c := by
        apply Finset.sum_le_sum
        intro d hd
        simpa only [norm_mul, residueWeight_norm, one_mul] using h d hd
      _ = (S.card : ℝ) * c := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hCard hc
  rw [norm_mul, prefactor, norm_div, norm_pow, norm_neg, norm_one, one_pow, hkC]
  calc
    _ ≤ (1 / (k : ℝ)) * ((2 * (k : ℝ)) * c) :=
      mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = _ := by field_simp [hkR.ne']

theorem term_at_zero (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k) :
    term S k 0 = weighted k (S k) * (delta k : ℂ) := by
  rw [term, weighted]
  simp only [difference_at_zero hk, ← Finset.sum_mul, mul_assoc]

theorem term_norm_le (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k)
    {q : ℂ} (hq : ‖q‖ ≤ 1 / 4) :
    ‖term S k q‖ ≤ (16 * fixedRadius * bound fixedRadius) * decay k := by
  have hPos : 0 ≤ (8 * fixedRadius * bound fixedRadius) * decay k :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Paper8FixedContourParameter.fixedRadius_pos.le)
      (Paper8ContourGammaRemainder.bound_nonneg Paper8FixedContourParameter.fixedRadius_pos))
      (Paper8ContourSignedDominance.decay_nonneg _)
  have h := norm_weighted_le hk (S k) (fun d => difference k (root k ^ (d.val : ℤ)) q) hPos
    (fun d _ => difference_norm_le hk (root_power_norm k d) hq)
  convert h using 1 <;> ring

theorem term_sub_zero_norm_le (S : ∀ k : ℕ, Finset (Fin (2 * k))) {k : ℕ} (hk : 0 < k)
    {q : ℂ} (hq : ‖q‖ ≤ 1 / 4) :
    ‖term S k q - term S k 0‖ ≤ (32 * fixedRadius * bound fixedRadius) * decay k * ‖q‖ := by
  have hEq : term S k q - term S k 0 =
      prefactor k * ∑ d ∈ S k, residueWeight k d *
        (difference k (root k ^ (d.val : ℤ)) q - difference k (root k ^ (d.val : ℤ)) 0) := by
    unfold term
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hPos : 0 ≤ (16 * fixedRadius * bound fixedRadius) * decay k * ‖q‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      Paper8FixedContourParameter.fixedRadius_pos.le)
      (Paper8ContourGammaRemainder.bound_nonneg Paper8FixedContourParameter.fixedRadius_pos))
      (Paper8ContourSignedDominance.decay_nonneg _)) (norm_nonneg _)
  rw [hEq]
  have h := norm_weighted_le hk (S k) (fun d =>
      difference k (root k ^ (d.val : ℤ)) q - difference k (root k ^ (d.val : ℤ)) 0) hPos
    (fun d _ => difference_sub_zero_norm_le hk (root_power_norm k d) hq)
  convert h using 1 <;> ring

end
end ManuscriptAudit.Paper8ContourDifferenceTerms

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ContourDifferenceTerms.term_at_zero,
      ``ManuscriptAudit.Paper8ContourDifferenceTerms.term_norm_le,
      ``ManuscriptAudit.Paper8ContourDifferenceTerms.term_sub_zero_norm_le] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
