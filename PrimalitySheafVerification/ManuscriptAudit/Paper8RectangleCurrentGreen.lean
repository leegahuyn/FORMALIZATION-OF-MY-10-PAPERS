import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PrimalitySheafVerification.ManuscriptAudit.RectangularIntegral

/-! The two-dimensional Green identity for a complex current on a closed rectangle. -/

namespace ManuscriptAudit.Paper8RectangleCurrentGreen

open Set MeasureTheory RectangularIntegral
open scoped Interval

theorem green_identity {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (P Q Px Qt : ℝ → ℝ → ℂ)
    (hPx : ContinuousOn Px.uncurry (rectangle a b c d))
    (hQt : ContinuousOn Qt.uncurry (rectangle a b c d))
    (hQ : ∀ x ∈ Icc a b, ∀ t ∈ Icc c d, HasDerivAt (fun s => Q s t) (Px x t) x)
    (hP : ∀ x ∈ Icc a b, ∀ t ∈ Icc c d, HasDerivAt (P x) (Qt x t) t) :
    box a b c d (fun z => Px z.1 z.2 - Qt z.1 z.2) =
      (∫ t in c..d, Q b t - Q a t) - (∫ x in a..b, P x d - P x c) := by
  have hX : box a b c d Px.uncurry = ∫ t in c..d, Q b t - Q a t := by
    rw [box_rows hab hcd hPx]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hcd] at ht
    have hLine : ContinuousOn (fun x : ℝ => Px x t) (uIcc a b) := by
      rw [uIcc_of_le hab]
      let L : ℝ → ℝ × ℝ := fun x => (x, t)
      have hCont : Continuous L := continuous_id.prodMk continuous_const
      have hMap : MapsTo L (Icc a b) (rectangle a b c d) := fun _ hx => ⟨hx, ht⟩
      exact hPx.comp hCont.continuousOn hMap
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hQ x (by simpa only [uIcc_of_le hab] using hx) t ht) hLine.intervalIntegrable
  have hT : box a b c d Qt.uncurry = ∫ x in a..b, P x d - P x c := by
    rw [box_columns hab hcd hQt]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hLine : ContinuousOn (Qt x) (uIcc c d) := by
      rw [uIcc_of_le hcd]
      let L : ℝ → ℝ × ℝ := fun t => (x, t)
      have hCont : Continuous L := continuous_const.prodMk continuous_id
      have hMap : MapsTo L (Icc c d) (rectangle a b c d) := fun _ ht => ⟨hx, ht⟩
      exact hQt.comp hCont.continuousOn hMap
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hP x hx t (by simpa only [uIcc_of_le hcd] using ht)) hLine.intervalIntegrable
  rw [← hX, ← hT]
  unfold box
  exact integral_sub (continuous_integrable hPx) (continuous_integrable hQt)

end ManuscriptAudit.Paper8RectangleCurrentGreen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8RectangleCurrentGreen.green_identity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
