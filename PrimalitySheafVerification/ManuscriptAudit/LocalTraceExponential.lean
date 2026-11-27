import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed

/-! The convergent scalar trace expansion underlying the finite local determinant. -/

namespace ManuscriptAudit.LocalTraceExponential

open Set Filter
open scoped Topology

noncomputable section

def term (n : ℕ) (z : ℂ) : ℂ := z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)

def traceLog (z : ℂ) : ℂ := ∑' n : ℕ, term n z

private theorem term_norm_bound {r : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖term n z‖ ≤ r ^ (n + 1) := by
  have hd : 1 ≤ ‖((n + 1 : ℕ) : ℂ)‖ := by simp
  calc
    _ ≤ ‖z ^ (n + 1)‖ := by
      rw [term, norm_div]
      exact div_le_self (norm_nonneg _) hd
    _ ≤ _ := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg z) hz _

private theorem shifted_geometric_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun n : ℕ => r ^ (n + 1)) := by
  simpa only [pow_succ'] using (summable_geometric_of_lt_one hr h₁).mul_left r

theorem term_norm_summable {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun n => ‖term n z‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_norm_bound le_rfl)
    (shifted_geometric_summable (norm_nonneg _) hz)

private theorem term_differentiable (n : ℕ) : Differentiable ℂ (term n) := by
  unfold term
  exact (differentiable_id.pow _).div_const _

private theorem term_deriv (n : ℕ) (z : ℂ) : deriv (term n) z = z ^ n := by
  have h := ((hasDerivAt_id z).pow (n + 1)).div_const (((n + 1 : ℕ) : ℂ))
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  change deriv (fun t : ℂ => t ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) z = z ^ n
  have he : deriv (fun t : ℂ => t ^ (n + 1) / ((n + 1 : ℕ) : ℂ)) z =
      (((n + 1 : ℕ) : ℂ) * z ^ ((n + 1) - 1) * 1) / ((n + 1 : ℕ) : ℂ) := h.deriv
  rw [he, Nat.add_sub_cancel, mul_one]
  field_simp [hn] <;> ring

theorem traceLog_hasDerivAt {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt traceLog (1 / (1 - z)) z := by
  let r := (‖z‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hzBall : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hBound (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) r) :
      ‖term n w‖ ≤ r ^ (n + 1) :=
    term_norm_bound (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hw).le) n
  have hGeom := shifted_geometric_summable hr hr₁
  have hFD (n : ℕ) : DifferentiableOn ℂ (term n) (Metric.ball 0 r) :=
    (term_differentiable n).differentiableOn
  have hd := Complex.hasSum_deriv_of_summable_norm (F := term)
    hGeom hFD Metric.isOpen_ball hBound hzBall
  change HasSum (fun n => deriv (term n) z) (deriv traceLog z) at hd
  simp only [term_deriv] at hd
  have he : deriv traceLog z = 1 / (1 - z) := by
    rw [← hd.tsum_eq, tsum_geometric_of_norm_lt_one hz, one_div]
  have hTrace := Complex.differentiableOn_tsum_of_summable_norm (F := term)
    hGeom hFD Metric.isOpen_ball hBound
  have h := ((hTrace z hzBall).differentiableAt (Metric.isOpen_ball.mem_nhds hzBall)).hasDerivAt
  change HasDerivAt traceLog (deriv traceLog z) z at h
  rwa [he] at h

theorem traceLog_zero : traceLog 0 = 0 := by
  unfold traceLog
  have h (n : ℕ) : term n 0 = 0 := by
    rw [term, zero_pow (Nat.succ_ne_zero n), zero_div]
  simp only [h, tsum_zero]

private theorem one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have he : z = 1 := (sub_eq_zero.mp h).symm
  simpa [he] using hz

theorem exp_traceLog {z : ℂ} (hz : ‖z‖ < 1) : Complex.exp (traceLog z) = (1 - z)⁻¹ := by
  let f : ℂ → ℂ := fun w => Complex.exp (traceLog w) * (1 - w)
  have hdf {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) : HasDerivAt f 0 w := by
    have hNorm : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
    have hSub : HasDerivAt (fun x : ℂ => 1 - x) (-1) w := by
      simpa only [zero_sub] using (hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)
    have h := ((traceLog_hasDerivAt hNorm).cexp).mul hSub
    have he : Complex.exp (traceLog w) * (1 / (1 - w)) * (1 - w) +
        Complex.exp (traceLog w) * (-1) = 0 := by
      field_simp [one_sub_ne_zero hNorm] <;> ring
    change HasDerivAt f _ w at h
    rwa [he] at h
  have hzBall : z ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
  have he := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    (fun w hw => (hdf hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hdf hw).deriv) hzBall h0
  have hpre : Complex.exp (traceLog z) * (1 - z) = 1 := by
    simpa only [f, traceLog_zero, Complex.exp_zero, sub_zero, mul_one] using he
  calc
    _ = (Complex.exp (traceLog z) * (1 - z)) * (1 - z)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (one_sub_ne_zero hz), mul_one]
    _ = _ := by rw [hpre, one_mul]

end
end ManuscriptAudit.LocalTraceExponential

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.LocalTraceExponential.term_norm_summable,
      ``ManuscriptAudit.LocalTraceExponential.traceLog_hasDerivAt,
      ``ManuscriptAudit.LocalTraceExponential.exp_traceLog] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
