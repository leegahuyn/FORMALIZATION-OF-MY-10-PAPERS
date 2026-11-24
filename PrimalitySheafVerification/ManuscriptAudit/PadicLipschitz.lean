import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.Spt1

namespace ManuscriptAudit.PadicLipschitz

open Spt1.PadicLog

variable {p : ℕ} [Fact (Nat.Prime p)]

private theorem norm_powers_sub_le_ball {x y : ℚ_[p]} {s : ℝ}
    (hs : 0 ≤ s) (hx : ‖x‖ ≤ s) (hy : ‖y‖ ≤ s) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ ‖x - y‖ * s ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hSplit :
        x ^ (n.succ + 1) - y ^ (n.succ + 1) =
          x ^ (n + 1) * (x - y) + y * (x ^ (n + 1) - y ^ (n + 1)) := by
      rw [show n.succ + 1 = (n + 1) + 1 by rfl, pow_succ x (n + 1), pow_succ y (n + 1)]
      ring
    have hLeft : ‖x ^ (n + 1) * (x - y)‖ ≤ ‖x - y‖ * s ^ n.succ := by
      rw [norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) (norm_nonneg _)
    have hRight : ‖y * (x ^ (n + 1) - y ^ (n + 1))‖ ≤ ‖x - y‖ * s ^ n.succ := by
      rw [norm_mul]
      calc
        ‖y‖ * ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ s * (‖x - y‖ * s ^ n) :=
          mul_le_mul hy ih (norm_nonneg _) hs
        _ = ‖x - y‖ * s ^ n.succ := by rw [pow_succ]; ring
    rw [hSplit]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hLeft hRight)

private theorem logarithm_term_difference_le {x y : ℚ_[p]}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (n : ℕ) :
    ‖padicLogSeries x n - padicLogSeries y n‖ ≤ ‖x - y‖ := by
  cases n with
  | zero => simp [padicLogSeries_zero_term]
  | succ n =>
    have hp : Nat.Prime p := Fact.out
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hBall (w : ℚ_[p]) (hw : ‖w‖ < 1) : ‖w‖ ≤ (p : ℝ)⁻¹ := by
      have h : ‖w‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
        rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
        simpa using hw
      simpa using h
    have hn : n.succ ≠ 0 := Nat.succ_ne_zero _
    have hCast : (n.succ : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hVal : padicValNat p n.succ ≤ n := by
      have hLt := (padicValNat_le_nat_log (p := p) n.succ).trans_lt (Nat.log_lt_self p hn)
      omega
    have hInv : ‖(n.succ : ℚ_[p])‖⁻¹ = (p : ℝ) ^ padicValNat p n.succ := by
      rw [Padic.norm_eq_zpow_neg_valuation hCast, Padic.valuation_natCast, zpow_neg, inv_inv,
        zpow_natCast]
    have hLog : padicLogSeries x n.succ - padicLogSeries y n.succ =
        ((-1 : ℚ_[p]) ^ (n.succ + 1) * (x ^ n.succ - y ^ n.succ)) / (n.succ : ℚ_[p]) := by
      unfold padicLogSeries
      ring
    rw [hLog]
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, div_eq_mul_inv, norm_inv,
      hInv]
    calc
      ‖x ^ n.succ - y ^ n.succ‖ * (p : ℝ) ^ padicValNat p n.succ ≤
          (‖x - y‖ * ((p : ℝ)⁻¹) ^ n) * (p : ℝ) ^ n :=
        mul_le_mul (norm_powers_sub_le_ball (inv_nonneg.mpr hpPos.le) (hBall x hx) (hBall y hy) n)
          (pow_le_pow_right₀ hpR hVal) (by positivity) (by positivity)
      _ = ‖x - y‖ := by
        rw [mul_assoc, inv_pow, inv_mul_cancel₀ (by positivity), mul_one]

/-- The actual p-adic logarithm series is 1-Lipschitz on its open unit disk. -/
theorem paper1_padic_log_one_lipschitz {x y : ℚ_[p]}
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ‖padicLog1p x - padicLog1p y‖ ≤ ‖x - y‖ := by
  have hSum := (padicLog1p_hasSum hx).sub (padicLog1p_hasSum hy)
  rw [← hSum.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _)
    (logarithm_term_difference_le hx hy)

end ManuscriptAudit.PadicLipschitz

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PadicLipschitz.paper1_padic_log_one_lipschitz
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
