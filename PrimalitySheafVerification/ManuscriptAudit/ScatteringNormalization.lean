import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

open MeasureTheory
open scoped BigOperators

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

/-- The same derivative on both printed normalizations forces the
continuous mass functional to vanish for every coefficient family. -/
theorem paper9_mass_zero_of_both_printed_density_formulas {A : Type*} [Fintype A]
    (trace : ℝ → ℂ) (Φ : ℝ → ℝ) (ρ : A → ℝ → ℂ)
    (h : ∀ t, criticalLineDensity (trace t) = analyticDensity (trace t)) :
    (∑ a : A, ∫ t : ℝ, Φ t * ‖ρ a t‖ ^ (2 : ℕ) *
      (analyticDensity (trace t)).re) = 0 := by
  have hTrace (t : ℝ) : trace t = 0 :=
    (paper9_displayed_scattering_densities_eq_iff_zero (trace t)).1 (h t)
  simp [hTrace, analyticDensity]

theorem paper9_real_trace_over_i_has_zero_real_part (trace : ℝ) :
    (criticalLineDensity (trace : ℂ)).re = 0 := by
  have h : analyticDensity (trace : ℂ) = ((trace / (4 * Real.pi) : ℝ) : ℂ) := by
    simp only [analyticDensity, Complex.ofReal_div]
  rw [criticalLineDensity, h, div_eq_mul_inv, Complex.inv_I, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, neg_zero, mul_zero, zero_mul, sub_zero]

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
  simp [analyticUnitaryExample, Complex.norm_exp, Complex.mul_re]

/-- Holomorphic differentiation can yield a negative real normalized
logarithmic derivative even with both scattering symmetries above. -/
theorem paper9_unitary_analytic_example_log_derivative_negative (s : ℂ) :
    deriv analyticUnitaryExample s * (analyticUnitaryExample s)⁻¹ = -1 := by
  have hLin : HasDerivAt (fun z : ℂ => 1 / 2 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 / 2 : ℂ)
  have h0 := (Complex.hasDerivAt_exp (1 / 2 - s)).comp s hLin
  change HasDerivAt analyticUnitaryExample (Complex.exp (1 / 2 - s) * (-1)) s at h0
  have hEq : Complex.exp (1 / 2 - s) * (-1) = -analyticUnitaryExample s := by
    simp [analyticUnitaryExample]
  have h := hEq ▸ h0
  have hne : analyticUnitaryExample s ≠ 0 := Complex.exp_ne_zero _
  rw [h.deriv, neg_mul, mul_inv_cancel₀ hne]

end

end ManuscriptAudit.ScatteringNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ScatteringNormalization.paper9_displayed_scattering_densities_eq_iff_zero,
      ``ManuscriptAudit.ScatteringNormalization.paper9_mass_zero_of_both_printed_density_formulas,
      ``ManuscriptAudit.ScatteringNormalization.paper9_real_trace_over_i_has_zero_real_part,
      ``ManuscriptAudit.ScatteringNormalization.analyticUnitaryExample_functional_equation,
      ``ManuscriptAudit.ScatteringNormalization.analyticUnitaryExample_unitary,
      ``ManuscriptAudit.ScatteringNormalization.paper9_unitary_analytic_example_log_derivative_negative] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
