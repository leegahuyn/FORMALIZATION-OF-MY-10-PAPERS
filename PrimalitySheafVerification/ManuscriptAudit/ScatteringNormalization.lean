import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Scattering density and the derivative convention

Paper 9, physical p. 415, divides the trace of the logarithmic
scattering derivative by 4πi. Physical pp. 421–422 and 425 divide
the same displayed derivative by 4π. If the prime means the same
derivative, the two densities agree only for trace zero.
-/

namespace ManuscriptAudit.ScatteringNormalization

noncomputable section

def analyticDensity (trace : ℂ) : ℂ := trace / ((4 * Real.pi : ℝ) : ℂ)

def criticalLineDensity (trace : ℂ) : ℂ := analyticDensity trace / Complex.I

theorem paper9_displayed_scattering_densities_eq_iff_zero (trace : ℂ) :
    criticalLineDensity trace = analyticDensity trace ↔ trace = 0 := by
  constructor
  · intro h
    change analyticDensity trace / Complex.I = analyticDensity trace at h
    have hScale := (div_eq_iff Complex.I_ne_zero).1 h
    have hProd : analyticDensity trace * (1 - Complex.I) = 0 := by
      rw [mul_sub, mul_one, ← hScale, sub_self]
    have hI : (1 : ℂ) - Complex.I ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      norm_num [Complex.sub_re] at hre
    have hz := (mul_eq_zero.mp hProd).resolve_right hI
    change trace / ((4 * Real.pi : ℝ) : ℂ) = 0 at hz
    have hπ : ((4 * Real.pi : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    simpa only [zero_mul] using (div_eq_iff hπ).1 hz
  · rintro rfl
    simp [criticalLineDensity, analyticDensity]

theorem paper9_real_trace_over_i_has_zero_real_part (trace : ℝ) :
    (criticalLineDensity (trace : ℂ)).re = 0 := by
  rw [criticalLineDensity, analyticDensity, ← Complex.ofReal_div, div_eq_mul_inv,
    Complex.inv_I]
  simp [Complex.mul_re]

/-- A nonzero holomorphic scalar family satisfying the scalar
functional equation and unitarity on the critical line. -/
def analyticUnitaryExample (s : ℂ) : ℂ := Complex.exp (1 / 2 - s)

theorem analyticUnitaryExample_functional_equation (s : ℂ) :
    analyticUnitaryExample s * analyticUnitaryExample (1 - s) = 1 := by
  unfold analyticUnitaryExample
  rw [← Complex.exp_add]
  rw [show (1 / 2 - s) + (1 / 2 - (1 - s)) = (0 : ℂ) by ring,
    Complex.exp_zero]

theorem analyticUnitaryExample_unitary (t : ℝ) :
    ‖analyticUnitaryExample (1 / 2 + Complex.I * (t : ℂ))‖ = 1 := by
  have h : (1 / 2 : ℂ) - (1 / 2 + Complex.I * (t : ℂ)) =
      -(Complex.I * (t : ℂ)) := by ring
  simp [analyticUnitaryExample, h, Complex.norm_exp, Complex.mul_re]

/-- Holomorphic differentiation can yield a negative real normalized
logarithmic derivative even with both scattering symmetries above. -/
theorem paper9_unitary_analytic_example_log_derivative_negative (s : ℂ) :
    deriv analyticUnitaryExample s * (analyticUnitaryExample s)⁻¹ = -1 := by
  have hLin : HasDerivAt (fun z : ℂ => 1 / 2 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 / 2 : ℂ)
  have h : HasDerivAt analyticUnitaryExample (-analyticUnitaryExample s) s := by
    simpa only [analyticUnitaryExample, Function.comp_def, mul_neg, mul_one] using
      (Complex.hasDerivAt_exp (1 / 2 - s)).comp s hLin
  have hne : analyticUnitaryExample s ≠ 0 := Complex.exp_ne_zero _
  rw [h.deriv, neg_mul, mul_inv_cancel₀ hne]

end

end ManuscriptAudit.ScatteringNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ScatteringNormalization.paper9_displayed_scattering_densities_eq_iff_zero,
      ``ManuscriptAudit.ScatteringNormalization.paper9_real_trace_over_i_has_zero_real_part,
      ``ManuscriptAudit.ScatteringNormalization.analyticUnitaryExample_functional_equation,
      ``ManuscriptAudit.ScatteringNormalization.analyticUnitaryExample_unitary,
      ``ManuscriptAudit.ScatteringNormalization.paper9_unitary_analytic_example_log_derivative_negative] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
