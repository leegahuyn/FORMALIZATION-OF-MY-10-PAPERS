import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-! Hasse-bounded elliptic Euler factors at one fixed nonzero complex argument. -/

namespace ManuscriptAudit.Paper7CommonEulerLocalDecay

open Filter Topology

/-- The denominator of the usual local quadratic Euler factor, at the common argument. -/
def denominator (q : ℕ) (a z : ℂ) : ℂ :=
  1 - a * z + (q : ℂ) * z^2

theorem factor_norm_le_half_of_large_card {q : ℕ} {a z : ℂ}
    (hHasse : ‖a‖ ≤ 2 * Real.sqrt (q : ℝ))
    (hLarge : 4 ≤ Real.sqrt (q : ℝ) * ‖z‖) :
    ‖(denominator q a z)⁻¹‖ ≤ 1 / 2 := by
  let X := Real.sqrt (q : ℝ) * ‖z‖
  have hLower : (q : ℝ) * ‖z‖^2 ≤ ‖denominator q a z‖ + (1 + ‖a‖ * ‖z‖) := by
    have hEq : (q : ℂ) * z^2 = denominator q a z - (1 - a * z) := by
      unfold denominator
      ring
    calc
      (q : ℝ) * ‖z‖^2 = ‖(q : ℂ) * z^2‖ := by
        rw [norm_mul, norm_pow] <;> simp
      _ = ‖denominator q a z - (1 - a * z)‖ := congrArg norm hEq
      _ ≤ ‖denominator q a z‖ + ‖1 - a * z‖ := norm_sub_le _ _
      _ ≤ ‖denominator q a z‖ + (1 + ‖a‖ * ‖z‖) := by
        apply add_le_add_left
        simpa only [norm_one, norm_mul] using norm_sub_le (1 : ℂ) (a * z)
  have hSq : X^2 = (q : ℝ) * ‖z‖^2 := by
    unfold X
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hLin : ‖a‖ * ‖z‖ ≤ 2 * X := by
    simpa only [X, mul_assoc] using mul_le_mul_of_nonneg_right hHasse (norm_nonneg z)
  have hX : 4 ≤ X := hLarge
  have hDen : 2 ≤ ‖denominator q a z‖ := by
    rw [← hSq] at hLower
    nlinarith only [hLower, hLin, hX, sq_nonneg (X - 4)]
  rw [norm_inv, ← one_div]
  apply (div_le_iff₀ (show 0 < ‖denominator q a z‖ by linarith)).mpr
  linarith

/-- At any fixed nonzero argument, all sufficiently late factors have norm at most one-half. -/
theorem eventually_factor_norm_le_half {q : ℕ → ℕ} {a : ℕ → ℂ}
    (hq : Tendsto (fun n => (q n : ℝ)) atTop atTop)
    (hHasse : ∀ n, ‖a n‖ ≤ 2 * Real.sqrt (q n : ℝ)) {z : ℂ} (hz : z ≠ 0) :
    ∀ᶠ n in atTop, ‖(denominator (q n) (a n) z)⁻¹‖ ≤ 1 / 2 := by
  let t : ℝ := ‖z‖
  have ht : 0 < t := norm_pos_iff.mpr hz
  have hP : ∀ᶠ n in atTop, (4 / t)^2 ≤ (q n : ℝ) :=
    (tendsto_atTop.1 hq) _
  filter_upwards [hP] with n hn
  apply factor_norm_le_half_of_large_card (hHasse n)
  have hs := Real.sqrt_le_sqrt hn
  rw [Real.sqrt_sq (show 0 ≤ 4 / t by positivity)] at hs
  exact (div_le_iff₀ ht).mp hs

end ManuscriptAudit.Paper7CommonEulerLocalDecay

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7CommonEulerLocalDecay.factor_norm_le_half_of_large_card,
      ``ManuscriptAudit.Paper7CommonEulerLocalDecay.eventually_factor_norm_le_half] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
