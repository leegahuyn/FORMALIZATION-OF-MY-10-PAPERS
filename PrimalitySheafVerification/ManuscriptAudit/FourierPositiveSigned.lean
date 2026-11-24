import Lean.Util.CollectAxioms
import Mathlib.Algebra.Star.Conjneg
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Paper 9, physical PDF p. 422. For a general compactly supported function,
a nonnegative Fourier transform does not imply that the function itself
is nonnegative. The witness is the autocorrelation of two signed pulses.
-/

namespace ManuscriptAudit.FourierPositiveSigned

open MeasureTheory Filter Set ContinuousLinearMap

open scoped ComplexConjugate Convolution FourierTransform

noncomputable section

private def box (a b : ℝ) : ℝ → ℂ :=
  (Icc a b).indicator (fun _ => 1)

private theorem box_integrable (a b : ℝ) : Integrable (box a b) := by
  unfold box
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (measure_Icc_lt_top (μ := volume)).ne)

/-- The signed input pulse. -/
def signedPulse : ℝ → ℂ :=
  box 0 1 - box 2 3

private theorem signedPulse_integrable : Integrable signedPulse :=
  (box_integrable 0 1).sub (box_integrable 2 3)

private theorem signedPulse_conj (t : ℝ) : conj (signedPulse t) = signedPulse t := by
  simp only [signedPulse, Pi.sub_apply, box, indicator_apply, map_sub]
  split_ifs <;> simp

private theorem signedPulse_zero_outside {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 3) :
    signedPulse t = 0 := by
  have h₁ : t ∉ Icc (0 : ℝ) 1 := fun h => ht ⟨h.1, h.2.trans (by norm_num)⟩
  have h₂ : t ∉ Icc (2 : ℝ) 3 := fun h => ht ⟨(by norm_num : (0 : ℝ) ≤ 2).trans h.1, h.2⟩
  simp [signedPulse, box, indicator_apply, h₁, h₂]

private theorem reflected_signedPulse_integrable : Integrable (conjneg signedPulse) := by
  have h : conjneg signedPulse = box (-1) 0 - box (-3) (-2) := by
    funext t
    have h₁ : -t ∈ Icc (0 : ℝ) 1 ↔ t ∈ Icc (-1 : ℝ) 0 := by
      simp only [mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have h₂ : -t ∈ Icc (2 : ℝ) 3 ↔ t ∈ Icc (-3 : ℝ) (-2) := by
      simp only [mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [conjneg_apply, signedPulse_conj, signedPulse, Pi.sub_apply, box, indicator_apply, h₁, h₂]
  rw [h]
  exact (box_integrable (-1) 0).sub (box_integrable (-3) (-2))

private theorem fourier_conjugate_reflection (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (conjneg f) ξ = conj (𝓕 f ξ) := by
  calc
    _ = 𝓕 (fun t => conj (f t)) (-ξ) := by
      exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ)
        (fun t : ℝ => conj (f t)) ξ
    _ = conj (𝓕 f ξ) := by
      rw [Real.fourier_real_eq_integral_exp_smul,
        Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
      apply integral_congr_ae
      filter_upwards with t
      simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
      apply congrArg (fun z : ℂ => Complex.exp z * conj (f t))
      simp only [Complex.ofReal_neg, Complex.ofReal_mul]
      ring

/-- The compactly supported signed autocorrelation. -/
def signedCorrelation : ℝ → ℂ :=
  signedPulse ⋆[mul ℂ ℂ] conjneg signedPulse

theorem signedCorrelation_integrable : Integrable signedCorrelation :=
  signedPulse_integrable.integrable_convolution (mul ℂ ℂ) reflected_signedPulse_integrable

/-- Its actual Fourier transform is pointwise the square of a norm. -/
theorem signedCorrelation_fourier (ξ : ℝ) :
    𝓕 signedCorrelation ξ = ((‖𝓕 signedPulse ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [signedCorrelation, Real.fourier_mul_convolution_eq signedPulse_integrable
    reflected_signedPulse_integrable, fourier_conjugate_reflection]
  simpa only [Complex.ofReal_pow] using Complex.mul_conj' (𝓕 signedPulse ξ)

private theorem autocorrelation_integrand_at_two (t : ℝ) :
    signedPulse t * conjneg signedPulse (2 - t) =
      (Icc (2 : ℝ) 3).indicator (fun _ => (-1 : ℂ)) t := by
  rw [conjneg_apply, signedPulse_conj]
  by_cases h₂ : t ∈ Icc (2 : ℝ) 3
  · have h₁ : t ∉ Icc (0 : ℝ) 1 := fun h => by linarith [h₂.1, h.2]
    have h₃ : -(2 - t) ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [h₂.1], by linarith [h₂.2]⟩
    have h₄ : -(2 - t) ∉ Icc (2 : ℝ) 3 := fun h => by linarith [h₂.2, h.1]
    simp [signedPulse, box, indicator_apply, h₁, h₂, h₃, h₄]
  · by_cases h₁ : t ∈ Icc (0 : ℝ) 1
    · have h₃ : -(2 - t) ∉ Icc (0 : ℝ) 1 := fun h => by linarith [h₁.2, h.1]
      have h₄ : -(2 - t) ∉ Icc (2 : ℝ) 3 := fun h => by linarith [h₁.2, h.1]
      simp [signedPulse, box, indicator_apply, h₁, h₂, h₃, h₄]
    · simp [signedPulse, box, indicator_apply, h₁, h₂]

/-- Yet its value at the real shift 2 is −1. -/
theorem signedCorrelation_at_two : signedCorrelation 2 = -1 := by
  change (∫ t : ℝ, signedPulse t * conjneg signedPulse (2 - t)) = -1
  calc
    _ = ∫ t : ℝ, (Icc (2 : ℝ) 3).indicator (fun _ => (-1 : ℂ)) t :=
      integral_congr_ae (Eventually.of_forall autocorrelation_integrand_at_two)
    _ = _ := by
      rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc]
      norm_num [Complex.real_smul]

/-- The correlation takes real values, as required of the test function. -/
theorem signedCorrelation_real (x : ℝ) : (signedCorrelation x).im = 0 := by
  have h : conj (signedCorrelation x) = signedCorrelation x := by
    change conj (∫ t : ℝ, signedPulse t * conjneg signedPulse (x - t)) =
      ∫ t : ℝ, signedPulse t * conjneg signedPulse (x - t)
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with t
    simp only [conjneg_apply, signedPulse_conj, map_mul]
  have he := congrArg Complex.im h
  simp only [Complex.conj_im] at he
  linarith

theorem signedCorrelation_compactSupport : HasCompactSupport signedCorrelation := by
  change IsCompact (closure (Function.support signedCorrelation))
  refine (isCompact_Icc : IsCompact (Icc (-3 : ℝ) 3)).of_isClosed_subset isClosed_closure
    (closure_minimal ?_ isClosed_Icc)
  intro x hx
  by_contra hxneg
  apply (Function.mem_support.mp hx)
  change (∫ t : ℝ, signedPulse t * conjneg signedPulse (x - t)) = 0
  calc
    _ = ∫ _ : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Icc (0 : ℝ) 3
      · have hout : -(x - t) ∉ Icc (0 : ℝ) 3 := by
          intro hu
          apply hxneg
          exact ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
        simp [conjneg_apply, signedPulse_zero_outside hout]
      · simp [signedPulse_zero_outside ht]
    _ = _ := integral_zero _ _

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``signedCorrelation_integrable, ``signedCorrelation_fourier,
      ``signedCorrelation_at_two, ``signedCorrelation_real,
      ``signedCorrelation_compactSupport] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.FourierPositiveSigned
