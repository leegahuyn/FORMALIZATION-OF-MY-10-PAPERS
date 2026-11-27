import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import PrimalitySheafVerification.ManuscriptAudit.Paper8InsideComplexComparison

/-!
# The exact translation phase of the p. 337 holomorphic part

The exponent is defined in the actual upper-half-plane parameter τ.
The displayed q-normalization contributes the phase exp(−πi/12).
-/

namespace ManuscriptAudit.Paper8HolomorphicPartPhase

open Paper8InsideComplexAnalytic Paper8InsideComplexComparison
open Paper8ExteriorNormalization (negPochhammer ramanujanTerm ramanujanF)

noncomputable section

def periodCoefficient : ℂ := 2 * (Real.pi : ℂ) * Complex.I

def qParameter (τ : ℂ) : ℂ := Complex.exp (periodCoefficient * τ)

def normalizationPhase : ℂ := Complex.exp (-(periodCoefficient / 24))

def normalizedPart (τ : ℂ) : ℂ :=
  Complex.exp (-(periodCoefficient / 24) * τ) * standard (qParameter τ)

theorem qParameter_add_one (τ : ℂ) : qParameter (τ + 1) = qParameter τ := by
  unfold qParameter
  rw [mul_add, mul_one, Complex.exp_add, periodCoefficient, Complex.exp_two_pi_mul_I, mul_one]

theorem normalizationPhase_eq_printed : normalizationPhase =
    Complex.exp (-(Real.pi : ℂ) * Complex.I / 12) := by
  unfold normalizationPhase periodCoefficient
  congr 1
  ring

theorem normalizedPart_add_one (τ : ℂ) :
    normalizedPart (τ + 1) = normalizationPhase * normalizedPart τ := by
  rw [normalizedPart, normalizedPart, qParameter_add_one, normalizationPhase,
    mul_add, mul_one, Complex.exp_add]
  ring

theorem normalizationPhase_ne_one : normalizationPhase ≠ 1 := by
  intro hPhase
  have h := congrArg Inv.inv hPhase
  have hExp : Complex.exp (periodCoefficient / 24) = 1 := by
    simpa only [normalizationPhase, Complex.exp_neg, inv_inv, inv_one] using h
  have hDvd : (24 : ℕ) ∣ (1 : ℕ) :=
    (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 1) (N := 24) (by decide)).mp
      (by simpa only [periodCoefficient, Nat.cast_one, mul_one] using hExp)
  exact (by decide : ¬ (24 : ℕ) ∣ (1 : ℕ)) hDvd

theorem qParameter_norm (τ : ℂ) :
    ‖qParameter τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [qParameter, Complex.norm_exp]
  congr 1
  norm_num [periodCoefficient, Complex.mul_re, Complex.mul_im] <;> ring

theorem qParameter_norm_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qParameter τ‖ < 1 := by
  rw [qParameter_norm]
  have h : -(2 * Real.pi * τ.im) < (0 : ℝ) :=
    neg_neg_of_pos (by positivity)
  simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr h

theorem normalizedPart_differentiableOn :
    DifferentiableOn ℂ normalizedPart {τ : ℂ | 0 < τ.im} := by
  have hExp (c : ℂ) : Differentiable ℂ (fun τ : ℂ => Complex.exp (c * τ)) :=
    Complex.differentiable_exp.comp ((differentiable_const (c := c)).mul differentiable_id)
  have hMaps : Set.MapsTo qParameter {τ : ℂ | 0 < τ.im} (Metric.ball (0 : ℂ) 1) := by
    intro τ hτ
    simpa only [Metric.mem_ball, dist_zero_right] using qParameter_norm_lt_one hτ
  exact (hExp (-(periodCoefficient / 24))).differentiableOn.mul
    (standard_differentiableOn_unit_disk.comp (hExp periodCoefficient).differentiableOn hMaps)

theorem normalizedPart_at_I_ne_zero : normalizedPart Complex.I ≠ 0 := by
  let r : ℝ := Real.exp (-(2 * Real.pi))
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := by
    have h : -(2 * Real.pi) < (0 : ℝ) := neg_neg_of_pos (by positivity)
    simpa only [r, Real.exp_zero] using Real.exp_lt_exp.mpr h
  have hParam : qParameter Complex.I = (r : ℂ) := by
    rw [qParameter, r, Complex.ofReal_exp]
    congr 1
    rw [periodCoefficient, mul_assoc, Complex.I_mul_I]
    push_cast
    ring
  have hS := (Paper8PrintedInsideSeries.printed_and_standard_summable hr.le hr₁).2
  have hOne : 1 ≤ ramanujanF r := by
    have hTerm := hS.le_tsum 0 (fun n _ =>
      div_nonneg (pow_nonneg hr.le (n ^ 2)) (sq_nonneg (negPochhammer r n)))
    simpa only [ramanujanF, ramanujanTerm, negPochhammer, pow_zero, Finset.range_zero,
      Finset.prod_empty, one_pow, div_one] using hTerm
  have hNZ : standard (qParameter Complex.I) ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    rw [hParam, standard_ofReal hr.le hr₁, Complex.ofReal_re, Complex.zero_re] at hRe
    exact (zero_lt_one.trans_le hOne).ne' hRe
  exact mul_ne_zero (Complex.exp_ne_zero _) hNZ

theorem normalizedPart_at_I_add_one_ne :
    normalizedPart (Complex.I + 1) ≠ normalizedPart Complex.I := by
  rw [normalizedPart_add_one]
  intro h
  apply normalizationPhase_ne_one
  exact mul_right_cancel₀ normalizedPart_at_I_ne_zero (by simpa only [one_mul] using h)

end
end ManuscriptAudit.Paper8HolomorphicPartPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8HolomorphicPartPhase.qParameter_add_one,
      ``ManuscriptAudit.Paper8HolomorphicPartPhase.normalizationPhase_eq_printed,
      ``ManuscriptAudit.Paper8HolomorphicPartPhase.normalizedPart_add_one,
      ``ManuscriptAudit.Paper8HolomorphicPartPhase.normalizationPhase_ne_one,
      ``ManuscriptAudit.Paper8HolomorphicPartPhase.qParameter_norm_lt_one,
      ``ManuscriptAudit.Paper8HolomorphicPartPhase.normalizedPart_differentiableOn,
      ``ManuscriptAudit.Paper8HolomorphicPartPhase.normalizedPart_at_I_ne_zero,
      ``ManuscriptAudit.Paper8HolomorphicPartPhase.normalizedPart_at_I_add_one_ne] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
