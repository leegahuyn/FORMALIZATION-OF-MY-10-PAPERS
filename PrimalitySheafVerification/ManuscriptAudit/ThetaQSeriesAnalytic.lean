import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Basic
import PrimalitySheafVerification.ManuscriptAudit.ThetaProfileGenerators

/-! The actual standard and alternating theta series have holomorphic cusp parameters. -/

namespace ManuscriptAudit.ThetaQSeriesAnalytic

open Set MeasureTheory
open Paper9ThetaCuspPhases ThetaProfileGenerators

noncomputable section

def cuspQ (τ : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * τ)

private def term (n : ℕ) (q : ℂ) : ℂ := q ^ ((n + 1) ^ 2)

private def squareSum (q : ℂ) : ℂ := ∑' n : ℕ, term n q

def thetaQ (q : ℂ) : ℂ := 1 + 2 * squareSum q

theorem norm_power_le_radius {m n : ℕ} (hmn : m ≤ n)
    {r : ℝ} (hr : r ≤ 1) {q : ℂ} (hq : ‖q‖ ≤ r) :
    ‖q ^ n‖ ≤ r ^ m := by
  have hR : 0 ≤ r := (norm_nonneg q).trans hq
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmn
  have hp : r ^ k ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hR hr k
  rw [norm_pow]
  calc
    _ ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg _) hq _
    _ = r ^ m * r ^ k := by rw [hk, pow_add]
    _ ≤ r ^ m * 1 := mul_le_mul_of_nonneg_left hp (pow_nonneg hR _)
    _ = _ := mul_one _

private theorem term_le_radius (n : ℕ) {r : ℝ} (hr : r ≤ 1) {q : ℂ} (hq : ‖q‖ ≤ r) :
    ‖term n q‖ ≤ r ^ (n + 1) :=
  norm_power_le_radius (by nlinarith : n + 1 ≤ (n + 1) ^ 2) hr hq

private theorem summable_radius {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun n : ℕ => r ^ (n + 1)) := by
  simpa only [pow_succ'] using (summable_geometric_of_lt_one hr h₁).mul_left r

private theorem term_differentiable (n : ℕ) :
    Differentiable ℂ (term n) := by
  unfold term
  fun_prop

private theorem squareSum_differentiableOn_ball {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    DifferentiableOn ℂ squareSum (Metric.ball (0 : ℂ) r) := by
  refine Complex.differentiableOn_tsum_of_summable_norm (F := term)
    (summable_radius hr h₁) (fun n => (term_differentiable n).differentiableOn)
    Metric.isOpen_ball ?_
  intro n q hq
  have h : ‖q‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hq
  exact term_le_radius n h₁.le h.le

theorem thetaQ_differentiableOn_unit_disk :
    DifferentiableOn ℂ thetaQ (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have h : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hq
  let r := (‖q‖ + 1) / 2
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hP := squareSum_differentiableOn_ball (r := r)
    (by dsimp [r]; positivity) (by dsimp [r]; linarith)
  have hD := (hP q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr)
  change DifferentiableWithinAt ℂ (fun x => 1 + 2 * squareSum x) (Metric.ball 0 1) q
  have hOne : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) q := differentiableAt_const _
  have hTwo : DifferentiableAt ℂ (fun _ : ℂ => (2 : ℂ)) q := differentiableAt_const _
  exact (hOne.add (hTwo.mul hD)).differentiableWithinAt

theorem thetaQ_zero : thetaQ 0 = 1 := by
  have ht : (fun n : ℕ => term n 0) = (fun _ : ℕ => (0 : ℂ)) := by
    funext n
    exact zero_pow (by positivity : (n + 1) ^ 2 ≠ 0)
  rw [thetaQ, squareSum, ht, tsum_zero, mul_zero, add_zero]

private theorem deriv_term_at_zero {n : ℕ} (h : n ≠ 0) : deriv (term n) 0 = 0 := by
  have h₂ : 2 ≤ n + 1 := by omega
  have h₄ : 4 ≤ (n + 1) ^ 2 := by
    simpa using pow_le_pow_left₀ (by decide : (0 : ℕ) ≤ 2) h₂ 2
  have hn : 0 < (n + 1) ^ 2 - 1 := by omega
  let k := (n + 1) ^ 2
  have hd := (hasDerivAt_id (0 : ℂ)).pow k
  change deriv ((id : ℂ → ℂ) ^ k) 0 = 0
  rw [hd.deriv]
  have hk : k - 1 ≠ 0 := hn.ne'
  simp only [id, zero_pow hk, mul_zero, zero_mul]

private theorem deriv_squareSum_at_zero : deriv squareSum 0 = 1 := by
  let r : ℝ := 1 / 2
  have h : 0 ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self (by norm_num [r])
  have hSum := Complex.hasSum_deriv_of_summable_norm (F := term)
    (summable_radius (by norm_num [r] : 0 ≤ r) (by norm_num [r] : r < 1))
    (fun n => (term_differentiable n).differentiableOn) Metric.isOpen_ball
    (fun n q hq => term_le_radius n (by norm_num [r] : r ≤ 1)
      (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hq).le)) h
  change HasSum (fun n => deriv (term n) 0) (deriv squareSum 0) at hSum
  rw [← hSum.tsum_eq]
  rw [tsum_eq_single 0]
  · have hTerm : term 0 = id := by
      funext z
      simp [term]
    rw [hTerm, (hasDerivAt_id (0 : ℂ)).deriv]
  · exact fun n hn => deriv_term_at_zero hn

theorem thetaQ_first_derivative : HasDerivAt thetaQ 2 0 := by
  have h : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 / 2) := Metric.mem_ball_self (by norm_num)
  have hD := ((squareSum_differentiableOn_ball (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num) 0 h).differentiableAt (Metric.isOpen_ball.mem_nhds h)).hasDerivAt
  change HasDerivAt ((fun _ : ℂ => (1 : ℂ)) + (fun q => 2 * squareSum q)) 2 0
  simpa only [deriv_squareSum_at_zero, mul_one, zero_add] using
    (hasDerivAt_const (0 : ℂ) (1 : ℂ)).add (hD.const_mul (2 : ℂ))

theorem jacobiTheta_eq_thetaQ {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ = thetaQ (cuspQ τ) := by
  have h (n : ℕ) : term n (cuspQ τ) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) ^ 2 * τ) := by
    unfold term cuspQ
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [jacobiTheta_eq_tsum_nat hτ, thetaQ, squareSum, h, Nat.cast_ofNat]

theorem thetaAlternating_eq_thetaQ_neg {τ : ℂ} (hτ : 0 < τ.im) :
    thetaAlternating τ = thetaQ (-cuspQ τ) := by
  have hShift : 0 < (τ + 1).im := by simpa using hτ
  rw [thetaAlternating, ← jacobiTheta_add_one_profile, jacobiTheta_eq_thetaQ hShift]
  congr 1
  rw [cuspQ, mul_add, Complex.exp_add, mul_one, Complex.exp_pi_mul_I, mul_neg_one, cuspQ]

end
end ManuscriptAudit.ThetaQSeriesAnalytic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaQSeriesAnalytic.norm_power_le_radius,
      ``ManuscriptAudit.ThetaQSeriesAnalytic.thetaQ_differentiableOn_unit_disk,
      ``ManuscriptAudit.ThetaQSeriesAnalytic.thetaQ_zero,
      ``ManuscriptAudit.ThetaQSeriesAnalytic.thetaQ_first_derivative,
      ``ManuscriptAudit.ThetaQSeriesAnalytic.jacobiTheta_eq_thetaQ,
      ``ManuscriptAudit.ThetaQSeriesAnalytic.thetaAlternating_eq_thetaQ_neg] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
