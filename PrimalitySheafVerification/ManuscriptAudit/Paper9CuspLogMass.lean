import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspLogTransform

/-! The logarithmic high-cusp profile has ordinary Euclidean mass in log-height. -/

namespace ManuscriptAudit.Paper9CuspLogMass

open Set Filter MeasureTheory Paper9EisensteinHeightEquation Paper9CuspLogTransform
open scoped UpperHalfPlane

noncomputable section

theorem weightedLogProfile_norm_sq (g : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    ‖weightedLogProfile g y‖ ^ (2 : ℕ) = y * ‖g (Real.log y)‖ ^ (2 : ℕ) := by
  have hE : criticalExponent 0 = (1 / 2 : ℂ) := by simp [criticalExponent]
  have h := critical_height_norm_sq 0 hy
  rw [hE] at h
  rw [weightedLogProfile, norm_mul, mul_pow, h]

theorem log_substitution (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ y : ℝ in a..b, f (Real.log y) * y⁻¹) = ∫ t : ℝ in Real.log a..Real.log b, f t := by
  have hy (y : ℝ) (hy : y ∈ uIcc a b) : y ≠ 0 := by
    rw [uIcc_of_le hab] at hy
    exact (ha.trans_le hy.1).ne'
  have hInv : ContinuousOn (fun y : ℝ => y⁻¹) (uIcc a b) :=
    continuousOn_inv₀.mono (fun y h => by simpa only [mem_compl_iff, mem_singleton_iff] using hy y h)
  exact intervalIntegral.integral_comp_mul_deriv
    (fun y h => Real.hasDerivAt_log (hy y h)) hInv hf

theorem finite_cusp_mass (g : ℝ → ℂ) (hg : Continuous g) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    2 * (∫ y : ℝ in a..b, ‖weightedLogProfile g y‖ ^ (2 : ℕ) / y ^ 2) =
      2 * ∫ t : ℝ in Real.log a..Real.log b, ‖g t‖ ^ (2 : ℕ) := by
  rw [← log_substitution (fun t => ‖g t‖ ^ (2 : ℕ)) (hg.norm.pow 2) ha hab]
  congr 1
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hab]
  intro y hy
  have hy₀ : 0 < y := ha.trans_le hy.1
  change ‖weightedLogProfile g y‖ ^ (2 : ℕ) / y ^ 2 = ‖g (Real.log y)‖ ^ (2 : ℕ) * y⁻¹
  rw [weightedLogProfile_norm_sq g hy₀]
  field_simp [hy₀.ne'] <;> ring

end
end ManuscriptAudit.Paper9CuspLogMass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspLogMass.weightedLogProfile_norm_sq,
      ``ManuscriptAudit.Paper9CuspLogMass.log_substitution,
      ``ManuscriptAudit.Paper9CuspLogMass.finite_cusp_mass] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
