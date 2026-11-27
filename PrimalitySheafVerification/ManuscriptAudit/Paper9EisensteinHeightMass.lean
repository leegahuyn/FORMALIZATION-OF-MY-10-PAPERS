import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoQuotientHeightIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper9EisensteinHeightEquation

/-! Critical height modes have logarithmically divergent mass on the genuine cusp. -/

namespace ManuscriptAudit.Paper9EisensteinHeightMass

open Set MeasureTheory GammaTwoHighStripMeasure GammaTwoQuotientHeightIntegral
open Paper9EisensteinHeightEquation Paper9HighCuspSection
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane

noncomputable section

private def clippedInv (B y : ℝ) : ℝ := if y ≤ B then y⁻¹ else 0

private def heightCut (B : ℝ) : Set ℍ := {z | z.im ≤ B}

private theorem heightCut_measurable (B : ℝ) : MeasurableSet (heightCut B) :=
  measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const

private theorem clipped_identity (B : ℝ) :
    (fun z : ℍ => z.im ^ 2 * clippedInv B z.im) =
      indicator (heightCut B) (fun z : ℍ => z.im) := by
  funext z
  by_cases hz : z.im ≤ B
  · rw [clippedInv, if_pos hz, indicator_of_mem (show z ∈ heightCut B from hz)]
    field_simp [z.im_ne_zero]
  · rw [clippedInv, if_neg hz, indicator_of_notMem (show z ∉ heightCut B from hz), mul_zero]

theorem clipped_mass (B : ℝ) (hB : 1 ≤ B) :
    (∫ z in strip, indicator (heightCut B) (fun z : ℍ => z.im) z ∂hyperbolicMeasure) =
      2 * Real.log B := by
  rw [← clipped_identity B, GammaTwoHighStripIntegral.height_integral,
    setIntegral_eq_interval (clippedInv B) hB
      (fun y hy => if_neg (not_le.mpr hy))]
  have he : (∫ y : ℝ in (1 : ℝ)..B, clippedInv B y) =
      ∫ y : ℝ in (1 : ℝ)..B, y⁻¹ := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hB]
    intro y hy
    exact if_pos hy.2
  rw [he, integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hB), div_one]

theorem cusp_height_nonintegrable : ¬ IntegrableOn (fun z : ℍ => z.im) strip hyperbolicMeasure := by
  intro h
  let μ := hyperbolicMeasure.restrict strip
  let M : ℝ := ∫ z : ℍ, z.im ∂μ
  let B : ℝ := Real.exp (|M| + 1)
  have hB : 1 ≤ B := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hClip : Integrable (indicator (heightCut B) (fun z : ℍ => z.im)) μ :=
    h.indicator (heightCut_measurable B)
  have hPoint (z : ℍ) : indicator (heightCut B) (fun z : ℍ => z.im) z ≤ z.im := by
    by_cases hz : z ∈ heightCut B
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      exact z.im_pos.le
  have hbound := integral_mono hClip h hPoint
  change (∫ z in strip, indicator (heightCut B) (fun z : ℍ => z.im) z ∂hyperbolicMeasure) ≤ M
    at hbound
  rw [clipped_mass B hB, show Real.log B = |M| + 1 from Real.log_exp _] at hbound
  linarith only [hbound, le_abs_self M, abs_nonneg M]

theorem critical_height_not_squareIntegrable (t : ℝ) :
    ¬ IntegrableOn (fun z : ℍ => ‖extendedSection (heightPower (criticalExponent t)) z‖ ^ (2 : ℕ))
      strip hyperbolicMeasure := by
  intro h
  apply cusp_height_nonintegrable
  apply h.congr
  exact (ae_restrict_iff' strip_measurable).mpr (Filter.Eventually.of_forall (fun z hz => by
    rw [extendedSection_at_high _ z (show 1 < z.im from hz.1),
      critical_height_norm_sq t z.im_pos]))

end
end ManuscriptAudit.Paper9EisensteinHeightMass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9EisensteinHeightMass.clipped_mass,
      ``ManuscriptAudit.Paper9EisensteinHeightMass.cusp_height_nonintegrable,
      ``ManuscriptAudit.Paper9EisensteinHeightMass.critical_height_not_squareIntegrable] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
