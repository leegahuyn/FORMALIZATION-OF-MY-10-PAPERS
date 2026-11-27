import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ComplexCorrectionProduct
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianRecurrenceTerms

/-! The p. 335 triangular correction is an actual holomorphic complex function. -/

namespace ManuscriptAudit.Paper8ComplexCorrection

open Paper8EulerianRecurrenceTerms (triangular triangular_formula le_triangular)
open Paper8ComplexCorrectionProduct (denominator denominator_ne_zero denominator_differentiableOn
  denominator_ofReal)
open Paper8ExteriorProductCorrection (correctionNumeratorTerm correctionNumerator_summable_abs
  productCorrection)

noncomputable section

def numeratorTerm (n : ℕ) (q : ℂ) : ℂ := (-1 : ℂ) ^ n * q ^ triangular n

def numerator (q : ℂ) : ℂ := ∑' n : ℕ, numeratorTerm n q

def correction (q : ℂ) : ℂ := numerator q / denominator q ^ 2

private theorem term_bound {q : ℂ} {r : ℝ} (hqr : ‖q‖ ≤ r) (h₁ : r < 1) (n : ℕ) :
    ‖numeratorTerm n q‖ ≤ r ^ n := by
  have hr : 0 ≤ r := (norm_nonneg q).trans hqr
  rw [numeratorTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg q) hqr _).trans
    (pow_le_pow_of_le_one hr h₁.le (le_triangular n))

theorem numerator_absolute_summable {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖numeratorTerm n q‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_bound le_rfl hq n)
    (summable_geometric_of_lt_one (norm_nonneg q) hq)

theorem numerator_differentiableOn :
    DifferentiableOn ℂ numerator (Metric.ball (0 : ℂ) 1) := by
  intro q hq
  have hq₁ : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  let r : ℝ := (‖q‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hqr : q ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hTerm (n : ℕ) : DifferentiableOn ℂ (numeratorTerm n) (Metric.ball (0 : ℂ) r) :=
    ((differentiable_const (c := (-1 : ℂ) ^ n)).mul
      (differentiable_id.pow (triangular n))).differentiableOn
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := numeratorTerm)
    (summable_geometric_of_lt_one hr hr₁) hTerm Metric.isOpen_ball (fun n z hz =>
      term_bound (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le) hr₁ n)
  exact ((h q hqr).differentiableAt (Metric.isOpen_ball.mem_nhds hqr)).differentiableWithinAt

theorem correction_differentiableOn :
    DifferentiableOn ℂ correction (Metric.ball (0 : ℂ) 1) := by
  refine numerator_differentiableOn.div (denominator_differentiableOn.pow 2) (fun q hq => ?_)
  have hNorm : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  exact pow_ne_zero 2 (denominator_ne_zero hNorm)

private theorem numeratorTerm_ofReal (q : ℝ) (n : ℕ) :
    ((correctionNumeratorTerm q n : ℝ) : ℂ) = numeratorTerm n (q : ℂ) := by
  simp only [correctionNumeratorTerm, numeratorTerm, triangular_formula, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]

theorem numerator_ofReal {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    numerator (q : ℂ) = ((∑' n : ℕ, correctionNumeratorTerm q n : ℝ) : ℂ) := by
  have hAbs : Summable (fun n => ‖correctionNumeratorTerm q n‖) := by
    simpa only [Real.norm_eq_abs] using correctionNumerator_summable_abs hq h₁
  have h := Complex.ofRealCLM.hasSum hAbs.of_norm.hasSum
  change HasSum (fun n => ((correctionNumeratorTerm q n : ℝ) : ℂ))
    ((∑' n : ℕ, correctionNumeratorTerm q n : ℝ) : ℂ) at h
  simp only [numeratorTerm_ofReal] at h
  exact h.tsum_eq

theorem correction_ofReal {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    correction (q : ℂ) = (productCorrection q : ℂ) := by
  rw [correction, numerator_ofReal hq h₁, denominator_ofReal hq h₁, productCorrection,
    Complex.ofReal_div, Complex.ofReal_pow]

end
end ManuscriptAudit.Paper8ComplexCorrection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ComplexCorrection.numerator_absolute_summable,
      ``ManuscriptAudit.Paper8ComplexCorrection.numerator_differentiableOn,
      ``ManuscriptAudit.Paper8ComplexCorrection.correction_differentiableOn,
      ``ManuscriptAudit.Paper8ComplexCorrection.correction_ofReal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
