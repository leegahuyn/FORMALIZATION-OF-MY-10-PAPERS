import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadow

/-! The printed unary shadow has an actual nonzero value in the upper half-plane. -/

namespace ManuscriptAudit.Paper8KroneckerShadowNonzero

open Paper8ExteriorNormalization (kroneckerNegTwelve)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8KroneckerShadow

noncomputable section

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [pow_succ]
      have hp : 1 ≤ (2 : ℕ) ^ n := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) _)
      omega

private theorem norm_quarter : ‖((1 / 4 : ℝ) : ℂ)‖ = (1 : ℝ) / 4 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]

private theorem tail_term_bound (n : ℕ) (hn : 2 ≤ n) :
    ‖shadowTerm n ((1 / 4 : ℝ) : ℂ)‖ ≤ ((1 : ℝ) / 8) ^ n := by
  rw [shadowTerm, norm_mul, norm_pow, norm_quarter]
  have hExp : 2 * n ≤ n ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right n hn
  have hCoeff : ‖coefficient n‖ ≤ (2 : ℝ) ^ n :=
    (norm_coefficient_le n).trans (by exact_mod_cast nat_le_two_pow n)
  calc
    _ ≤ (2 : ℝ) ^ n * ((1 : ℝ) / 4) ^ (2 * n) := mul_le_mul hCoeff
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hExp) (by positivity) (by positivity)
    _ = _ := by rw [pow_mul, ← mul_pow]; norm_num

private theorem shadowTerm_zero (w : ℂ) : shadowTerm 0 w = 0 := by
  simp [shadowTerm, coefficient]

private theorem shadowTerm_one (w : ℂ) : shadowTerm 1 w = w := by
  have hChi : kroneckerNegTwelve 1 = 1 := by
    norm_num [kroneckerNegTwelve, jacobiSym.one_right]
  norm_num [shadowTerm, coefficient, hChi]

private theorem series_split {w : ℂ} (hw : ‖w‖ < 1) :
    shadowSeries w = w + ∑' k : ℕ, shadowTerm (k + 2) w := by
  have hSum : Summable (fun n : ℕ => shadowTerm n w) :=
    (shadowSeries_absolute_summability hw).of_norm
  have hTail : Summable (fun n : ℕ => shadowTerm (n + 1) w) := (summable_nat_add_iff 1).mpr hSum
  have hFirst : shadowSeries w = shadowTerm 0 w + (∑' n : ℕ, shadowTerm (n + 1) w) :=
    hSum.tsum_eq_zero_add
  have hSecond : (∑' n : ℕ, shadowTerm (n + 1) w) =
      shadowTerm 1 w + (∑' k : ℕ, shadowTerm (k + 2) w) :=
    hTail.tsum_eq_zero_add
  calc
    _ = shadowTerm 0 w + (∑' n : ℕ, shadowTerm (n + 1) w) := hFirst
    _ = w + (∑' k : ℕ, shadowTerm (k + 2) w) := by
      rw [shadowTerm_zero, zero_add, hSecond, shadowTerm_one]

private theorem quarter_real_majorant :
    HasSum (fun k : ℕ => ((1 : ℝ) / 8) ^ (k + 2)) ((1 : ℝ) / 56) := by
  have hGeom := (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 : ℝ) / 8)
    (by norm_num : (1 : ℝ) / 8 < 1)).mul_right (((1 : ℝ) / 8) ^ (2 : ℕ))
  have hValue : (1 - (1 : ℝ) / 8)⁻¹ * ((1 : ℝ) / 8) ^ (2 : ℕ) = 1 / 56 := by
    norm_num
  simpa only [pow_add, hValue] using hGeom

private theorem quarter_tail_bound :
    ‖∑' k : ℕ, shadowTerm (k + 2) ((1 / 4 : ℝ) : ℂ)‖ ≤ (1 : ℝ) / 56 :=
  tsum_of_norm_bounded quarter_real_majorant (fun k => tail_term_bound (k + 2) (by omega))

theorem shadowSeries_at_quarter_ne_zero : shadowSeries ((1 / 4 : ℝ) : ℂ) ≠ 0 := by
  let w : ℂ := ((1 / 4 : ℝ) : ℂ)
  have hw : ‖w‖ < 1 := by change ‖((1 / 4 : ℝ) : ℂ)‖ < 1; rw [norm_quarter]; norm_num
  have hDecomp := series_split hw
  change shadowSeries w ≠ 0
  intro h
  have hAdd : w + (∑' k : ℕ, shadowTerm (k + 2) w) = w + -w := by
    rw [← hDecomp, h, add_neg_cancel]
  have hTailValue := add_left_cancel hAdd
  have hBound : ‖∑' k : ℕ, shadowTerm (k + 2) w‖ ≤ (1 : ℝ) / 56 := quarter_tail_bound
  rw [hTailValue, norm_neg] at hBound
  change ‖((1 / 4 : ℝ) : ℂ)‖ ≤ (1 : ℝ) / 56 at hBound
  rw [norm_quarter] at hBound
  norm_num at hBound

theorem unaryShadow_nonzero_on_upper_half_plane :
    ∃ τ : ℂ, 0 < τ.im ∧ unaryShadow τ ≠ 0 := by
  let t : ℝ := -(12 / Real.pi) * Real.log (1 / 4)
  have ht : 0 < t := mul_pos_of_neg_of_neg (neg_neg_of_pos (by positivity))
    (Real.log_neg (by norm_num) (by norm_num))
  let τ : ℂ := (t : ℂ) * Complex.I
  have hτ : 0 < τ.im := by simpa [τ, Complex.mul_im] using ht
  have hLog : -(Real.pi * t / 12) = Real.log (1 / 4) := by
    dsimp [t]
    field_simp [Real.pi_ne_zero] <;> ring
  have hRoot : rootParameter τ = ((1 / 4 : ℝ) : ℂ) := by
    calc
      _ = (Real.exp (-(Real.pi * t / 12)) : ℂ) := by
        rw [rootParameter, Complex.ofReal_exp]
        congr 1
        change (periodCoefficient / 24) * ((t : ℂ) * Complex.I) = _
        unfold periodCoefficient
        push_cast
        linear_combination ((Real.pi : ℂ) * (t : ℂ) / 12) * Complex.I_mul_I
      _ = _ := by rw [hLog, Real.exp_log (by norm_num)]
  refine ⟨τ, hτ, ?_⟩
  rw [unaryShadow, hRoot]
  exact shadowSeries_at_quarter_ne_zero

end
end ManuscriptAudit.Paper8KroneckerShadowNonzero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8KroneckerShadowNonzero.shadowSeries_at_quarter_ne_zero,
      ``ManuscriptAudit.Paper8KroneckerShadowNonzero.unaryShadow_nonzero_on_upper_half_plane] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
