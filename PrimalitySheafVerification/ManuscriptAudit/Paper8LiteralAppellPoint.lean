import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimalitySheafVerification.ManuscriptAudit.AppellSameIntegerShift
import PrimalitySheafVerification.ManuscriptAudit.Paper8AppellRealModel

/-! An admissible nonzero point for the literal p. 339 Appell quotient with even theta. -/

namespace ManuscriptAudit.Paper8LiteralAppellPoint

open AppellSameIntegerShift (numeratorTerm numerator)

noncomputable section

private abbrev phaseUnit : ℂ := (Real.pi : ℂ) * Complex.I

def sampleHeight : ℝ := -Real.log (1 / 4) / Real.pi

def sampleTau : ℂ := (sampleHeight : ℂ) * Complex.I

abbrev sampleU : ℂ := (-1 : ℂ) / 2

theorem sampleHeight_pos : 0 < sampleHeight := by
  unfold sampleHeight
  exact div_pos (neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))) Real.pi_pos

theorem sampleTau_im_pos : 0 < sampleTau.im := by
  simpa [sampleTau, Complex.mul_im] using sampleHeight_pos

theorem sample_half_nome : Complex.exp (phaseUnit * sampleTau) = (1 / 4 : ℝ) := by
  have hLog : -Real.pi * sampleHeight = Real.log (1 / 4) := by
    unfold sampleHeight
    field_simp [Real.pi_ne_zero] <;> ring
  have hPhase : phaseUnit * sampleTau = ((-Real.pi * sampleHeight : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (Real.pi : ℂ) * sampleHeight * Complex.I ^ 2 := by unfold sampleTau; ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hPhase, ← Complex.ofReal_exp, hLog, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 4)]

private theorem denominator_phase (n : ℤ) :
    phaseUnit * (2 * (sampleU + (n : ℂ) * sampleTau)) =
      -phaseUnit + (((2 * n : ℤ) : ℂ) * (phaseUnit * sampleTau)) := by
  push_cast
  ring

theorem sample_pole_denominator (n : ℤ) :
    1 - Complex.exp (phaseUnit * (2 * (sampleU + (n : ℂ) * sampleTau))) =
      ((1 + (1 / 4 : ℝ) ^ (2 * n) : ℝ) : ℂ) := by
  rw [denominator_phase, Complex.exp_add, Complex.exp_neg_pi_mul_I, Complex.exp_int_mul,
    sample_half_nome, neg_one_mul, sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_zpow]

theorem sample_pole_denominator_ne_zero (n : ℤ) :
    1 - Complex.exp (phaseUnit * (2 * (sampleU + (n : ℂ) * sampleTau))) ≠ 0 := by
  rw [sample_pole_denominator]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

theorem sample_shifted_pole_denominator_ne_zero (n : ℤ) :
    1 - Complex.exp (phaseUnit * (2 * (sampleU + sampleTau + (n : ℂ) * sampleTau))) ≠ 0 := by
  have h : sampleU + sampleTau + (n : ℂ) * sampleTau =
      sampleU + ((n + 1 : ℤ) : ℂ) * sampleTau := by push_cast; ring
  rw [h]
  exact sample_pole_denominator_ne_zero (n + 1)

theorem sample_numerator_term (n : ℤ) :
    numeratorTerm sampleU 0 sampleTau n = (Paper8AppellRealModel.term (1 / 4) n : ℂ) := by
  have hNum : phaseUnit * (((n : ℂ) ^ 2 + n) * sampleTau + 2 * (n : ℂ) * 0) =
      (((n ^ 2 + n : ℤ) : ℂ) * (phaseUnit * sampleTau)) := by push_cast; ring
  change ((-1 : ℂ) ^ n * Complex.exp
    (phaseUnit * (((n : ℂ) ^ 2 + n) * sampleTau + 2 * (n : ℂ) * 0))) /
      (1 - Complex.exp (phaseUnit * (2 * (sampleU + (n : ℂ) * sampleTau)))) = _
  rw [hNum, Complex.exp_int_mul, sample_half_nome, sample_pole_denominator]
  simp only [Paper8AppellRealModel.term, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_zpow, Complex.ofReal_neg, Complex.ofReal_one]

theorem sample_numerator_eq :
    numerator sampleU 0 sampleTau = ((∑' n : ℤ, Paper8AppellRealModel.term (1 / 4) n : ℝ) : ℂ) := by
  have ha := Paper8AppellRealModel.abs_summable (r := 1 / 4) (by norm_num) (by norm_num)
  have h := Complex.ofRealCLM.hasSum ha.of_norm.hasSum
  change HasSum (fun n : ℤ => (Paper8AppellRealModel.term (1 / 4) n : ℂ))
    ((∑' n : ℤ, Paper8AppellRealModel.term (1 / 4) n : ℝ) : ℂ) at h
  exact (h.congr_fun sample_numerator_term).tsum_eq

theorem sample_numerator_ne_zero : numerator sampleU 0 sampleTau ≠ 0 := by
  rw [sample_numerator_eq]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt Paper8AppellRealModel.tsum_quarter_pos)

private theorem sample_theta_term (n : ℤ) :
    jacobiTheta₂_term n 0 sampleTau =
      (Real.exp (-Real.pi * sampleHeight * (n : ℝ) ^ 2) : ℂ) := by
  rw [jacobiTheta₂_term, Complex.ofReal_exp]
  congr 1
  push_cast
  calc
    _ = (Real.pi : ℂ) * (n : ℂ) ^ 2 * sampleHeight * Complex.I ^ 2 := by unfold sampleTau; ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem sample_theta_re_pos : 0 < (jacobiTheta₂ 0 sampleTau).re := by
  have hh := hasSum_jacobiTheta₂_term 0 sampleTau_im_pos
  have hr : HasSum (fun n : ℤ => Real.exp (-Real.pi * sampleHeight * (n : ℝ) ^ 2))
      (jacobiTheta₂ 0 sampleTau).re := by
    simpa only [Complex.reCLM_apply, sample_theta_term, Complex.ofReal_re] using
      Complex.reCLM.hasSum hh
  have hle := hr.summable.sum_le_tsum ({0} : Finset ℤ) (fun n _ => (Real.exp_pos
    (-Real.pi * sampleHeight * (n : ℝ) ^ 2)).le)
  rw [hr.tsum_eq, Finset.sum_singleton] at hle
  exact (Real.exp_pos _).trans_le hle

theorem sample_theta_ne_zero : jacobiTheta₂ 0 sampleTau ≠ 0 := by
  intro h
  apply (ne_of_gt sample_theta_re_pos)
  rw [h, Complex.zero_re]

end
end ManuscriptAudit.Paper8LiteralAppellPoint

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8LiteralAppellPoint.sampleTau_im_pos,
      ``ManuscriptAudit.Paper8LiteralAppellPoint.sample_half_nome,
      ``ManuscriptAudit.Paper8LiteralAppellPoint.sample_pole_denominator_ne_zero,
      ``ManuscriptAudit.Paper8LiteralAppellPoint.sample_shifted_pole_denominator_ne_zero,
      ``ManuscriptAudit.Paper8LiteralAppellPoint.sample_numerator_eq,
      ``ManuscriptAudit.Paper8LiteralAppellPoint.sample_numerator_ne_zero,
      ``ManuscriptAudit.Paper8LiteralAppellPoint.sample_theta_ne_zero] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
