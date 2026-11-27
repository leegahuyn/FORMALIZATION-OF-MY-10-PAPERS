import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9PrincipalThetaStrip

/-! At two complementary imaginary heights the principal modulo-four theta fails the printed S norm law. -/

namespace ManuscriptAudit.Paper9PrincipalThetaInversion

open Complex Paper9PrincipalThetaStrip

noncomputable section

theorem norm_principalTheta_axis_le_geometric (y : ℝ) (hy : 0 < y) :
    ‖principalTheta ((y : ℂ) * I)‖ ≤
      2 * (Real.exp (-Real.pi * y) / (1 - Real.exp (-Real.pi * y))) := by
  let τ := (y : ℂ) * I
  let a (n : ℤ) := principalChar n * jacobiTheta₂_term n 0 τ
  let f (n : ℤ) := ‖a n‖
  let r := Real.exp (-Real.pi * y)
  have hr₀ : 0 < r := Real.exp_pos _
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (by
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hy)
  have hchar (n : ℤ) : ‖principalChar n‖ ≤ 1 := by
    by_cases hn : n % 2 = 1 <;> simp [principalChar, hn]
  have hmajor : Summable (fun n : ℤ => ‖jacobiTheta₂_term n 0 τ‖) :=
    (summable_norm_iff (E := ℂ)).2 ((summable_jacobiTheta₂_term_iff 0 τ).2 (by simpa [τ] using hy))
  have hA : Summable a := hmajor.of_norm_bounded fun n => by
    change ‖principalChar n * jacobiTheta₂_term n 0 τ‖ ≤ _
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hchar n) (norm_nonneg _)
  have hF : Summable f := (summable_norm_iff (E := ℂ)).2 hA
  have h0 : f 0 = 0 := by simp [f, a, principalChar]
  let b (n : ℕ) := f (n : ℤ) + f (-(n : ℤ))
  have hb : HasSum b (∑' n : ℤ, f n) := by
    have h := hF.hasSum.nat_add_neg
    simpa only [b, h0, add_zero] using h
  have hb0 : b 0 = 0 := by simp [b, h0]
  have htail : HasSum (fun n : ℕ => b (n + 1)) (∑' n : ℤ, f n) := by
    apply (hasSum_nat_add_iff 1).mpr
    simpa only [Finset.sum_range_one, hb0, zero_add, add_zero] using hb
  have hExp (n : ℤ) :
      f n ≤ Real.exp (-Real.pi * ((n : ℝ) ^ 2) * y) := by
    change ‖principalChar n * jacobiTheta₂_term n 0 τ‖ ≤ _
    rw [norm_mul, norm_jacobiTheta₂_term]
    have hτ : τ.im = y := by simp [τ]
    rw [hτ, Complex.zero_im, mul_zero, sub_zero]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hchar n) (Real.exp_pos _).le
  have hm (n : ℕ) (k : ℤ) (hk : (n + 1 : ℝ) ≤ (k : ℝ) ^ 2) :
      f k ≤ r ^ (n + 1) := by
    refine (hExp k).trans ?_
    rw [show r ^ (n + 1) = Real.exp (-Real.pi * (n + 1 : ℝ) * y) by
      dsimp [r]
      rw [← Real.exp_nat_mul]
      push_cast
      ring]
    have H := mul_le_mul_of_nonneg_right hk (mul_nonneg Real.pi_pos.le hy.le)
    exact Real.exp_le_exp.mpr (by nlinarith only [H])
  have hc (n : ℕ) : b (n + 1) ≤ 2 * r ^ (n + 1) := by
    have hx : (n + 1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
    have hl := hm n ((n + 1 : ℕ) : ℤ) (by push_cast; exact hx)
    have hu := hm n (-((n + 1 : ℕ) : ℤ)) (by push_cast; simpa only [neg_sq] using hx)
    change f ((n + 1 : ℕ) : ℤ) + f (-((n + 1 : ℕ) : ℤ)) ≤ _
    linarith
  have hGeom : HasSum (fun n : ℕ => 2 * r ^ (n + 1)) (2 * (r / (1 - r))) := by
    have h := hasSum_geometric_of_lt_one hr₀.le hr
    simpa only [pow_succ', div_eq_mul_inv] using (h.mul_left r).mul_left 2
  calc
    ‖principalTheta τ‖ ≤ ∑' n : ℤ, f n := norm_tsum_le_tsum_norm hF
    _ = ∑' n : ℕ, b (n + 1) := htail.tsum_eq.symm
    _ ≤ 2 * (r / (1 - r)) := (htail.summable.tsum_mono hGeom.summable hc).trans_eq hGeom.tsum_eq

theorem fails_printed_inversion_norm_at_two :
    Real.sqrt 2 * ‖principalTheta ((2 : ℂ) * I)‖ <
      ‖principalTheta (((1 / 2 : ℝ) : ℂ) * I)‖ := by
  let r := Real.exp (-(2 * Real.pi))
  have h₀ : 0 < r := Real.exp_pos _
  have hr : r < 1 / 5 := by
    have hExp : 5 < Real.exp (2 * Real.pi) :=
      (by linarith [Real.pi_gt_three] : (5 : ℝ) < 2 * Real.pi + 1).trans_le (Real.add_one_le_exp _)
    dsimp [r]
    rw [Real.exp_neg]
    simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 5) hExp
  have hs : Real.sqrt (2 : ℝ) ≤ 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)
    simpa using h
  have hN : ‖principalTheta ((2 : ℂ) * I)‖ ≤ 2 * (r / (1 - r)) := by
    have h := norm_principalTheta_axis_le_geometric 2 (by norm_num)
    convert h using 2 <;> simp [r, mul_comm]
  have hFive : 4 * (r / (1 - r)) < 5 * r := by
    rw [← mul_div_assoc]
    exact (div_lt_iff₀ (by linarith : 0 < 1 - r)).mpr (by nlinarith)
  have hExp : 5 * r < Real.exp (-Real.pi * (1 / 2)) := by
    have hh : 5 < Real.exp (3 * Real.pi / 2) :=
      (by linarith [Real.pi_gt_three] : (5 : ℝ) < 3 * Real.pi / 2 + 1).trans_le
        (Real.add_one_le_exp _)
    have h := mul_lt_mul_of_pos_right hh h₀
    dsimp [r] at h
    rwa [← Real.exp_add, show 3 * Real.pi / 2 + -(2 * Real.pi) = -Real.pi * (1 / 2) by ring] at h
  calc
    _ ≤ 2 * ‖principalTheta ((2 : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ 4 * (r / (1 - r)) := by nlinarith only [hN]
    _ < 5 * r := hFive
    _ < Real.exp (-Real.pi * (1 / 2)) := hExp
    _ ≤ _ :=
      (principalTheta_re_axis_lower (1 / 2) (by norm_num)).trans (Complex.re_le_norm _)

end
end ManuscriptAudit.Paper9PrincipalThetaInversion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9PrincipalThetaInversion.norm_principalTheta_axis_le_geometric,
      ``ManuscriptAudit.Paper9PrincipalThetaInversion.fails_printed_inversion_norm_at_two] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
