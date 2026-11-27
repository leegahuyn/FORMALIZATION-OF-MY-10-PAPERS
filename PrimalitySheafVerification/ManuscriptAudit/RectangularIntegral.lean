import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Prod

/-! Bochner integration on a closed rectangle, with both interval slicings. -/

namespace ManuscriptAudit.RectangularIntegral

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rectangle (a b c d : ℝ) : Set (ℝ × ℝ) :=
  Icc a b ×ˢ Icc c d

noncomputable def box (a b c d : ℝ) (f : ℝ × ℝ → E) : E :=
  ∫ z in rectangle a b c d, f z

theorem continuous_integrable {a b c d : ℝ} {f : ℝ × ℝ → E}
    (hf : ContinuousOn f (rectangle a b c d)) :
    IntegrableOn f (rectangle a b c d) :=
  hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem box_congr {a b c d : ℝ} {f g : ℝ × ℝ → E}
    (h : Set.EqOn f g (rectangle a b c d)) :
    box a b c d f = box a b c d g :=
  setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) h

theorem box_add {a b c d : ℝ} {f g : ℝ × ℝ → E}
    (hf : ContinuousOn f (rectangle a b c d))
    (hg : ContinuousOn g (rectangle a b c d)) :
    box a b c d (fun z => f z + g z) = box a b c d f + box a b c d g :=
  integral_add (continuous_integrable hf) (continuous_integrable hg)

theorem box_columns {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {f : ℝ × ℝ → E} (hf : ContinuousOn f (rectangle a b c d)) :
    box a b c d f = ∫ x in a..b, ∫ y in c..d, f (x, y) := by
  have hi := continuous_integrable hf
  rw [Measure.volume_eq_prod] at hi
  unfold box rectangle at *
  rw [Measure.volume_eq_prod, setIntegral_prod f hi]
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    integral_Icc_eq_integral_Ioc]

theorem box_rows {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {f : ℝ × ℝ → E} (hf : ContinuousOn f (rectangle a b c d)) :
    box a b c d f = ∫ y in c..d, ∫ x in a..b, f (x, y) := by
  rw [box_columns hab hcd hf]
  apply intervalIntegral_intervalIntegral_swap
  simpa only [Function.uncurry_curry, uIoc_of_le hab, uIoc_of_le hcd] using
    (continuous_integrable hf).mono_set
      (fun _ hz => ⟨Ioc_subset_Icc_self hz.1, Ioc_subset_Icc_self hz.2⟩ :
        Ioc a b ×ˢ Ioc c d ⊆ rectangle a b c d)

end ManuscriptAudit.RectangularIntegral

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RectangularIntegral.box_add,
      ``ManuscriptAudit.RectangularIntegral.box_columns,
      ``ManuscriptAudit.RectangularIntegral.box_rows] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
