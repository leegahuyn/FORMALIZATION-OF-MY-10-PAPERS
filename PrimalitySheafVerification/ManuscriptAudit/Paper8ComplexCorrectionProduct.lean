import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplex
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorProductCorrection

/-! The actual complex product denominator in the p. 335 correction is holomorphic and nonzero. -/

namespace ManuscriptAudit.Paper8ComplexCorrectionProduct

open Paper8ExteriorComplex (radius_power_le)
open Paper8ExteriorProductCorrection (correctionProduct correctionProduct_multipliable)

noncomputable section

def denominator (q : ℂ) : ℂ := ∏' n : ℕ, (1 + q ^ (n + 1))

private def logTerm (n : ℕ) (q : ℂ) : ℂ := Complex.log (1 + q ^ (n + 1))

private def logSeries (q : ℂ) : ℂ := ∑' n : ℕ, logTerm n q

private def majorant (r : ℝ) (n : ℕ) : ℝ := ((1 - r)⁻¹ / 2 + 1) * r ^ (n + 1)

private theorem norm_power_lt_one {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    ‖q ^ (n + 1)‖ < 1 := by
  rw [norm_pow]
  exact (radius_power_le (norm_nonneg q) hq.le n).trans_lt hq

private theorem log_bound {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (h₁ : r < 1) (n : ℕ) :
    ‖logTerm n q‖ ≤ majorant r n := by
  have hr : 0 ≤ r := (norm_nonneg q).trans hqr
  let z : ℂ := q ^ (n + 1)
  have hPow : ‖z‖ ≤ r ^ (n + 1) := by
    change ‖q ^ (n + 1)‖ ≤ r ^ (n + 1)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg q) hqr _
  have hzr : ‖z‖ ≤ r := hPow.trans (radius_power_le hr h₁.le n)
  have hz : ‖z‖ < 1 := hzr.trans_lt h₁
  have hInv : (1 - ‖z‖)⁻¹ ≤ (1 - r)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (sub_pos.mpr h₁) (sub_le_sub_left hzr 1)
  have hSq : ‖z‖ ^ 2 ≤ ‖z‖ := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hz.le (norm_nonneg z)
  have hMul : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ ≤ r ^ (n + 1) * (1 - r)⁻¹ :=
    mul_le_mul (hSq.trans hPow) hInv (inv_nonneg.mpr (sub_nonneg.mpr hz.le)) (pow_nonneg hr _)
  calc
    _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := Complex.norm_log_one_add_le hz
    _ ≤ r ^ (n + 1) * (1 - r)⁻¹ / 2 + r ^ (n + 1) :=
      add_le_add (div_le_div_of_nonneg_right hMul (by norm_num)) hPow
    _ = _ := by unfold majorant; ring

private theorem majorant_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (majorant r) := by
  change Summable (fun n : ℕ => ((1 - r)⁻¹ / 2 + 1) * r ^ (n + 1))
  simpa only [pow_succ', mul_assoc] using
    (summable_geometric_of_lt_one hr h₁).mul_left (((1 - r)⁻¹ / 2 + 1) * r)

private theorem log_absolute_summable {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖logTerm n q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => log_bound le_rfl hq n)
    (majorant_summable (norm_nonneg q) hq)

private theorem logSeries_differentiableOn :
    DifferentiableOn ℂ logSeries (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hq₁ : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hTerm (n : ℕ) : DifferentiableOn ℂ (logTerm n) (Metric.ball (0 : ℂ) r) := by
    intro z hz
    have hz' : ‖z‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hSlit : 1 + z ^ (n + 1) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_of_norm_lt_one (norm_power_lt_one (hz'.trans hr₁) n)
    have hp : DifferentiableAt ℂ (fun t : ℂ => 1 + t ^ (n + 1)) z :=
      (differentiableAt_const (c := (1 : ℂ))).add (differentiableAt_id.pow (n + 1))
    exact ((Complex.differentiableAt_log hSlit).comp z hp).differentiableWithinAt
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := logTerm)
    (majorant_summable hr hr₁) hTerm Metric.isOpen_ball (fun n z hz =>
      log_bound (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le) hr₁ n)
  exact ((h q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr)).differentiableWithinAt

private theorem exp_logSeries_eq_denominator {q : ℂ} (hq : ‖q‖ < 1) :
    Complex.exp (logSeries q) = denominator q := by
  unfold logSeries logTerm denominator
  apply Complex.cexp_tsum_eq_tprod
  · intro n
    exact Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one (norm_power_lt_one hq n))
  · exact (log_absolute_summable hq).of_norm

theorem denominator_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : denominator q ≠ 0 := by
  rw [← exp_logSeries_eq_denominator hq]
  exact Complex.exp_ne_zero _

theorem denominator_differentiableOn :
    DifferentiableOn ℂ denominator (Metric.ball (0 : ℂ) 1) := by
  have hExp : DifferentiableOn ℂ (fun q => Complex.exp (logSeries q)) (Metric.ball (0 : ℂ) 1) := by
    intro q hq
    have h := (logSeries_differentiableOn q hq).differentiableAt (Metric.isOpen_ball.mem_nhds hq)
    exact (Complex.differentiable_exp.differentiableAt.comp q h).differentiableWithinAt
  refine hExp.congr fun q hq => ?_
  have hNorm : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  exact (exp_logSeries_eq_denominator hNorm).symm

theorem denominator_ofReal {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    denominator (q : ℂ) = (correctionProduct q : ℂ) := by
  have h := (correctionProduct_multipliable hq h₁).hasProd.map Complex.ofRealHom Complex.continuous_ofReal
  change HasProd (fun n : ℕ => ((1 + q ^ (n + 1) : ℝ) : ℂ)) (correctionProduct q : ℂ) at h
  simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow] at h
  exact h.tprod_eq

end
end ManuscriptAudit.Paper8ComplexCorrectionProduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ComplexCorrectionProduct.denominator_ne_zero,
      ``ManuscriptAudit.Paper8ComplexCorrectionProduct.denominator_differentiableOn,
      ``ManuscriptAudit.Paper8ComplexCorrectionProduct.denominator_ofReal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
