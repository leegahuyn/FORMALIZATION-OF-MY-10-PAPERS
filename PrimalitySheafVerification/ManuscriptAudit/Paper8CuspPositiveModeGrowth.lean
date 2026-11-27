import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Positive Fourier modes of a conjugate holomorphic cusp function

The coefficient below is the conjugate of a positive mode of an
anti-holomorphic profile. A rectangular Cauchy integral gives exact
exponential growth with height whenever the coefficient is nonzero.
-/

namespace ManuscriptAudit.Paper8CuspPositiveModeGrowth

open Set MeasureTheory
open scoped Interval

noncomputable section

def conjugatePositiveMode (H : ℂ → ℂ) (frequency y : ℝ) : ℂ :=
  ∫ x : ℝ in (0 : ℝ)..1,
    H ((x : ℂ) + (y : ℂ) * Complex.I) * Complex.exp ((frequency : ℂ) * Complex.I * (x : ℂ))

def HasTwistedTranslation (H : ℂ → ℂ) (frequency : ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    H (z + 1) = Complex.exp (-((frequency : ℂ) * Complex.I)) * H z

private def twist (H : ℂ → ℂ) (frequency : ℝ) (z : ℂ) : ℂ :=
  H z * Complex.exp ((frequency : ℂ) * Complex.I * z)

private theorem twist_periodic (H : ℂ → ℂ) (frequency : ℝ) (hT : HasTwistedTranslation H frequency)
    {z : ℂ} (hz : 0 < z.im) :
    twist H frequency (z + 1) = twist H frequency z := by
  unfold twist
  rw [hT z hz, show (frequency : ℂ) * Complex.I * (z + 1) =
    (frequency : ℂ) * Complex.I * z + (frequency : ℂ) * Complex.I by ring, Complex.exp_add]
  have hExp : Complex.exp (-((frequency : ℂ) * Complex.I)) *
      Complex.exp ((frequency : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc
    _ = H z * Complex.exp ((frequency : ℂ) * Complex.I * z) *
        (Complex.exp (-((frequency : ℂ) * Complex.I)) * Complex.exp ((frequency : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [hExp, mul_one]

private theorem twist_integral_factor (H : ℂ → ℂ) (frequency y : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..1, twist H frequency ((x : ℂ) + (y : ℂ) * Complex.I)) =
      (Real.exp (-frequency * y) : ℂ) * conjugatePositiveMode H frequency y := by
  rw [conjugatePositiveMode, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  unfold twist
  have hArg : (frequency : ℂ) * Complex.I * ((x : ℂ) + (y : ℂ) * Complex.I) =
      (frequency : ℂ) * Complex.I * (x : ℂ) + ((-frequency * y : ℝ) : ℂ) := by
    calc
      _ = (frequency : ℂ) * Complex.I * (x : ℂ) + (frequency : ℂ) * (y : ℂ) * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; push_cast; ring
  rw [hArg, Complex.exp_add, Complex.ofReal_exp]
  ring

theorem positive_mode_balanced (H : ℂ → ℂ) (frequency : ℝ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) (hT : HasTwistedTranslation H frequency)
    {y₀ y₁ : ℝ} (h₀ : 0 < y₀) (h₁ : 0 < y₁) :
    (Real.exp (-frequency * y₀) : ℂ) * conjugatePositiveMode H frequency y₀ =
      (Real.exp (-frequency * y₁) : ℂ) * conjugatePositiveMode H frequency y₁ := by
  let G := twist H frequency
  have hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} := by
    unfold G twist
    have hLin : Differentiable ℂ (fun z : ℂ => (frequency : ℂ) * Complex.I * z) := by fun_prop
    exact hH.mul (Complex.differentiable_exp.comp hLin).differentiableOn
  have hRect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    (⟨0, y₀⟩ : ℂ) (⟨1, y₁⟩ : ℂ) (hG.mono (by
      intro z hz
      change 0 < z.im
      change z.re ∈ uIcc (0 : ℝ) 1 ∧ z.im ∈ uIcc y₀ y₁ at hz
      exact (lt_min h₀ h₁).trans_le (mem_uIcc.mp hz.2).1))
  have hVert : (∫ v : ℝ in y₀..y₁, G ((1 : ℂ) + (v : ℂ) * Complex.I)) =
      ∫ v : ℝ in y₀..y₁, G ((v : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun v hv => ?_)
    have hV : 0 < v := (lt_min h₀ h₁).trans_le (mem_uIcc.mp hv).1
    have hZ : 0 < (((v : ℂ) * Complex.I).im) := by
      simpa [Complex.mul_im] using hV
    rw [add_comm]
    exact twist_periodic H frequency hT hZ
  change (∫ x : ℝ in (0 : ℝ)..1, G ((x : ℂ) + (y₀ : ℂ) * Complex.I)) -
      (∫ x : ℝ in (0 : ℝ)..1, G ((x : ℂ) + (y₁ : ℂ) * Complex.I)) +
      Complex.I • (∫ v : ℝ in y₀..y₁, G ((1 : ℂ) + (v : ℂ) * Complex.I)) -
      Complex.I • (∫ v : ℝ in y₀..y₁, G ((0 : ℂ) + (v : ℂ) * Complex.I)) = 0 at hRect
  rw [zero_add, hVert, add_sub_cancel_right, sub_eq_zero] at hRect
  simpa only [G, twist_integral_factor] using hRect

theorem positive_mode_exponential_growth (H : ℂ → ℂ) (frequency : ℝ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) (hT : HasTwistedTranslation H frequency)
    {y₀ y₁ : ℝ} (h₀ : 0 < y₀) (h₁ : 0 < y₁) :
    conjugatePositiveMode H frequency y₁ =
      (Real.exp (frequency * (y₁ - y₀)) : ℂ) * conjugatePositiveMode H frequency y₀ := by
  have hEq := positive_mode_balanced H frequency hH hT h₀ h₁
  have hPos : (Real.exp (frequency * y₁) : ℂ) * (Real.exp (-frequency * y₁) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show frequency * y₁ + -frequency * y₁ = 0 by ring,
      Real.exp_zero, Complex.ofReal_one]
  have hFactor : (Real.exp (frequency * y₁) : ℂ) * (Real.exp (-frequency * y₀) : ℂ) =
      (Real.exp (frequency * (y₁ - y₀)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show frequency * y₁ + -frequency * y₀ = frequency * (y₁ - y₀) by ring]
  have h := congrArg (fun z : ℂ => (Real.exp (frequency * y₁) : ℂ) * z) hEq
  simpa only [← mul_assoc, hPos, hFactor, one_mul] using h.symm

end
end ManuscriptAudit.Paper8CuspPositiveModeGrowth

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8CuspPositiveModeGrowth.positive_mode_balanced,
      ``ManuscriptAudit.Paper8CuspPositiveModeGrowth.positive_mode_exponential_growth] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
