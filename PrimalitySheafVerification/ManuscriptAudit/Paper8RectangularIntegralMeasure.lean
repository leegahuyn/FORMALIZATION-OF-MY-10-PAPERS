import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Prod
import PrimalitySheafVerification.ManuscriptAudit.Paper8RectangularGridApproximation

/-! A closed rectangular coordinate integral agrees with its product-space restriction. -/

namespace ManuscriptAudit.Paper8RectangularIntegralMeasure

open MeasureTheory Set Paper8RectangularGridApproximation
open scoped ENNReal

noncomputable section

theorem rectangleIntegral_eq_setIntegral {f : ℝ → ℝ → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    rectangleIntegral f a b c d = ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, f p.1 p.2 := by
  let μ := (volume : Measure ℝ).restrict (Icc a b)
  let ν := (volume : Measure ℝ).restrict (Icc c d)
  have hI : Integrable (fun p : ℝ × ℝ => f p.1 p.2) (μ.prod ν) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have h := integral_prod_symm (fun p : ℝ × ℝ => f p.1 p.2) hI
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  simpa only [μ, ν, rectangleIntegral, intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    ← integral_Icc_eq_integral_Ioc] using h.symm

theorem ofReal_rectangleIntegral_eq_lintegral {f : ℝ → ℝ → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) (hf₀ : ∀ x y, 0 ≤ f x y)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ENNReal.ofReal (rectangleIntegral f a b c d) =
      ∫⁻ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, ENNReal.ofReal (f p.1 p.2) := by
  rw [rectangleIntegral_eq_setIntegral hf hab hcd]
  exact ofReal_integral_eq_lintegral_ofReal
    (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (Filter.Eventually.of_forall fun p => hf₀ p.1 p.2)

end
end ManuscriptAudit.Paper8RectangularIntegralMeasure

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8RectangularIntegralMeasure.ofReal_rectangleIntegral_eq_lintegral
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
