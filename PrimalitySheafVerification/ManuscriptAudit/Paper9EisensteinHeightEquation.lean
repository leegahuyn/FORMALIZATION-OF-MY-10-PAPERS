import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspCoordinates

/-!
# Native differential equation for the Eisenstein height terms

These are exact statements in the actual positive-height cusp chart,
including the sign of the printed differential expression on the
critical line and the pointwise size of each critical height mode.
-/

namespace ManuscriptAudit.Paper9EisensteinHeightEquation

open Set Filter Paper9HighCuspCoordinates Paper9PrintedLaplacianSign Paper9HighCuspSection
open scoped UpperHalfPlane Topology

noncomputable section

def heightPower (s : ℂ) (y : ℝ) : ℂ := Complex.exp ((Real.log y : ℂ) * s)

theorem heightPower_eq_cpow (s : ℂ) {y : ℝ} (hy : 0 < y) :
    heightPower s y = (y : ℂ) ^ s := by
  have hC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [heightPower, Complex.cpow_def_of_ne_zero hC, Complex.ofReal_log hy.le]

theorem heightPower_hasDerivAt (s : ℂ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (heightPower s) (heightPower s y * ((y : ℂ)⁻¹ * s)) y := by
  have h := ((Real.hasDerivAt_log hy).ofReal_comp.mul_const s).cexp
  simpa only [heightPower, Complex.ofReal_inv] using h

theorem heightPower_second (s : ℂ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (heightPower s)) y =
      s * (s - 1) * heightPower s y / (y : ℂ) ^ 2 := by
  have hLocal : deriv (heightPower s) =ᶠ[𝓝 y]
      (fun t : ℝ => heightPower s t * ((t : ℂ)⁻¹ * s)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (heightPower_hasDerivAt s (ne_of_gt ht)).deriv
  have hC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hinv := ((hasDerivAt_id y).ofReal_comp).inv hC
  have h := (heightPower_hasDerivAt s hy.ne').mul (hinv.mul_const s)
  rw [hLocal.deriv_eq, h.deriv]
  simp only [id_eq, Complex.ofReal_one]
  field_simp [hC] <;> ring

/-- The zero horizontal mode in the actual high-cusp chart. -/
theorem printedL_heightPower (s : ℂ) (z : ℍ) (hz : 1 < z.im) :
    printedL (coordinates (heightPower s)) z =
      s * (s - 1) * extendedSection (heightPower s) z := by
  have hC : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
  rw [printedL_high _ z hz, heightPower_second s z.im_pos, extendedSection_at_high _ z hz]
  field_simp [hC]

def criticalExponent (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * Complex.I

theorem critical_exponent_product (t : ℝ) :
    criticalExponent t * (criticalExponent t - 1) =
      -((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
  unfold criticalExponent
  push_cast
  calc
    _ = -1 / 4 + (t : ℂ) ^ 2 * (Complex.I * Complex.I) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem printedL_critical_height (t : ℝ) (z : ℍ) (hz : 1 < z.im) :
    printedL (coordinates (heightPower (criticalExponent t))) z =
      -((1 / 4 + t ^ 2 : ℝ) : ℂ) * extendedSection (heightPower (criticalExponent t)) z := by
  rw [printedL_heightPower _ z hz, critical_exponent_product]

theorem critical_height_norm_sq (t : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖heightPower (criticalExponent t) y‖ ^ (2 : ℕ) = y := by
  have h : (((Real.log y : ℝ) : ℂ) * criticalExponent t).re = Real.log y / 2 := by
    simp [criticalExponent, Complex.add_re, Complex.mul_re, Complex.div_re] <;> ring
  rw [heightPower, Complex.norm_exp, h, pow_two, ← Real.exp_add]
  rw [show Real.log y / 2 + Real.log y / 2 = Real.log y by ring, Real.exp_log hy]

end
end ManuscriptAudit.Paper9EisensteinHeightEquation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9EisensteinHeightEquation.heightPower_eq_cpow,
      ``ManuscriptAudit.Paper9EisensteinHeightEquation.heightPower_hasDerivAt,
      ``ManuscriptAudit.Paper9EisensteinHeightEquation.heightPower_second,
      ``ManuscriptAudit.Paper9EisensteinHeightEquation.printedL_heightPower,
      ``ManuscriptAudit.Paper9EisensteinHeightEquation.critical_exponent_product,
      ``ManuscriptAudit.Paper9EisensteinHeightEquation.printedL_critical_height,
      ``ManuscriptAudit.Paper9EisensteinHeightEquation.critical_height_norm_sq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
