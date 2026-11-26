import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Pi.Bounds
import PrimalitySheafVerification.ManuscriptAudit.ThetaProfileGenerators

/-! The three genuine theta profiles have no zeros above height two thirds. -/

namespace ManuscriptAudit.ThetaProfilesNonzero

open Paper9ThetaCuspPhases ThetaProfileGenerators

noncomputable section

private theorem exp_neg_height_lt_third {τ : ℂ} (hτ : (2 / 3 : ℝ) < τ.im) :
    Real.exp (-Real.pi * τ.im) < 1 / 3 := by
  have hy : 0 < τ.im := (by norm_num : (0 : ℝ) < 2 / 3).trans hτ
  have hx : 2 < Real.pi * τ.im := by
    have h := mul_lt_mul_of_pos_right Real.pi_gt_three hy
    linarith
  have he : 3 < Real.exp (Real.pi * τ.im) :=
    (show (3 : ℝ) < Real.pi * τ.im + 1 by linarith).trans
      (Real.add_one_lt_exp (by linarith))
  rw [neg_mul, Real.exp_neg, one_div]
  exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).mpr he

theorem jacobiTheta_sub_one_norm_lt_one_at_height {τ : ℂ} (hτ : (2 / 3 : ℝ) < τ.im) :
    ‖jacobiTheta τ - 1‖ < 1 := by
  have hy : 0 < τ.im := (by norm_num : (0 : ℝ) < 2 / 3).trans hτ
  let q := Real.exp (-Real.pi * τ.im)
  have hq : q < 1 / 3 := exp_neg_height_lt_third hτ
  refine (norm_jacobiTheta_sub_one_le hy).trans_lt ?_
  change 2 / (1 - q) * q < 1
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ (by linarith : 0 < 1 - q)).mpr (by linarith)

theorem jacobiTheta_ne_zero_at_height {τ : ℂ} (hτ : (2 / 3 : ℝ) < τ.im) :
    jacobiTheta τ ≠ 0 := by
  intro hz
  simpa [hz] using jacobiTheta_sub_one_norm_lt_one_at_height hτ

theorem thetaAlternating_ne_zero_at_height {τ : ℂ} (hτ : (2 / 3 : ℝ) < τ.im) :
    thetaAlternating τ ≠ 0 := by
  rw [thetaAlternating, ← jacobiTheta_add_one_profile]
  exact jacobiTheta_ne_zero_at_height (by simpa using hτ)

private def normalizedHalfTerm (n : ℤ) (τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ) * ((n : ℂ) + 1) * τ)

private theorem normalizedHalfTerm_eq (n : ℤ) (τ : ℂ) :
    normalizedHalfTerm n τ = jacobiTheta₂_term n (τ / 2) τ := by
  unfold normalizedHalfTerm jacobiTheta₂_term
  congr 1
  ring

private theorem normalizedHalfTerm_norm (n : ℤ) (τ : ℂ) :
    ‖normalizedHalfTerm n τ‖ =
      Real.exp (-Real.pi * (n : ℝ) * ((n : ℝ) + 1) * τ.im) := by
  have h : (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((n : ℂ) + 1) * τ =
      Complex.ofReal (Real.pi * (n : ℝ) * ((n : ℝ) + 1)) * τ * Complex.I := by
    push_cast
    ring
  rw [normalizedHalfTerm, h, Complex.norm_exp, Complex.mul_I_re, Complex.im_ofReal_mul]
  congr 1
  ring

private theorem normalizedHalfTerm_flip (n : ℕ) (τ : ℂ) :
    normalizedHalfTerm (-(↑n + 1)) τ = normalizedHalfTerm (n : ℤ) τ := by
  unfold normalizedHalfTerm
  congr 1
  push_cast
  ring

private theorem thetaHalfShift_pair {τ : ℂ} (hτ : 0 < τ.im) :
    thetaHalfShift τ = Complex.exp ((Real.pi : ℂ) * Complex.I * τ / 4) *
      (2 * ∑' n : ℕ, normalizedHalfTerm (n : ℤ) τ) := by
  have hs : HasSum (fun n : ℤ => normalizedHalfTerm n τ) (jacobiTheta₂ (τ / 2) τ) := by
    simpa only [normalizedHalfTerm_eq] using hasSum_jacobiTheta₂_term (τ / 2) hτ
  have hp := hs.nat_add_neg_add_one
  rw [thetaHalfShift, ← hp.tsum_eq]
  simp_rw [normalizedHalfTerm_flip, ← two_mul]
  rw [tsum_mul_left]

private theorem norm_halfTail {τ : ℂ} (hτ : 0 < τ.im) :
    ‖∑' n : ℕ, normalizedHalfTerm ((n : ℤ) + 1) τ‖ ≤
      Real.exp (-Real.pi * τ.im) / (1 - Real.exp (-Real.pi * τ.im)) := by
  let q := Real.exp (-Real.pi * τ.im)
  have hlt : q < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hτ)
  have hs : HasSum (fun n : ℕ => q ^ (n + 1)) (q / (1 - q)) := by
    have h := hasSum_geometric_of_lt_one (show 0 ≤ q from (Real.exp_pos _).le) hlt
    simpa only [pow_succ', div_eq_mul_inv] using h.mul_left q
  have hd (n : ℕ) : ‖normalizedHalfTerm ((n : ℤ) + 1) τ‖ ≤ q ^ (n + 1) := by
    rw [normalizedHalfTerm_norm]
    change _ ≤ Real.exp (-Real.pi * τ.im) ^ (n + 1)
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have h1 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
      nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg Real.pi_pos.le hτ.le)
    nlinarith only [h2]
  have hAbs : Summable (fun n : ℕ => ‖normalizedHalfTerm ((n : ℤ) + 1) τ‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _) hd hs.summable
  exact (norm_tsum_le_tsum_norm hAbs).trans
    ((hAbs.tsum_mono hs.summable hd).trans_eq hs.tsum_eq)

theorem thetaHalfShift_ne_zero_at_height {τ : ℂ} (hτ : (2 / 3 : ℝ) < τ.im) :
    thetaHalfShift τ ≠ 0 := by
  have hy : 0 < τ.im := (by norm_num : (0 : ℝ) < 2 / 3).trans hτ
  have hs : Summable (fun n : ℤ => normalizedHalfTerm n τ) := by
    simpa only [normalizedHalfTerm_eq] using
      (hasSum_jacobiTheta₂_term (τ / 2) hy).summable
  have hNat : Summable (fun n : ℕ => normalizedHalfTerm (n : ℤ) τ) :=
    hs.comp_injective (show Function.Injective (fun n : ℕ => (n : ℤ)) from
      fun _ _ h => Int.ofNat.inj h)
  have hSplit : (∑' n : ℕ, normalizedHalfTerm (n : ℤ) τ) =
      1 + ∑' n : ℕ, normalizedHalfTerm ((n : ℤ) + 1) τ := by
    rw [hNat.tsum_eq_zero_add]
    simp [normalizedHalfTerm, Nat.cast_add]
  let q := Real.exp (-Real.pi * τ.im)
  have hq : q < 1 / 3 := exp_neg_height_lt_third hτ
  have hTail : ‖∑' n : ℕ, normalizedHalfTerm ((n : ℤ) + 1) τ‖ < 1 :=
    (norm_halfTail hy).trans_lt
      ((div_lt_iff₀ (by linarith : 0 < 1 - q)).mpr (by linarith))
  rw [thetaHalfShift_pair hy]
  refine mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (by norm_num) ?_)
  intro h
  rw [hSplit] at h
  have hNeg : (∑' n : ℕ, normalizedHalfTerm ((n : ℤ) + 1) τ) = -1 := by
    linear_combination h
  simpa [hNeg] using hTail

end
end ManuscriptAudit.ThetaProfilesNonzero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaProfilesNonzero.jacobiTheta_sub_one_norm_lt_one_at_height,
      ``ManuscriptAudit.ThetaProfilesNonzero.jacobiTheta_ne_zero_at_height,
      ``ManuscriptAudit.ThetaProfilesNonzero.thetaAlternating_ne_zero_at_height,
      ``ManuscriptAudit.ThetaProfilesNonzero.thetaHalfShift_ne_zero_at_height] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
