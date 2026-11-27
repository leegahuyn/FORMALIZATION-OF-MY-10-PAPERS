import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import PrimalitySheafVerification.ManuscriptAudit.ProjectedTwistedTrace

/-! Exact witnesses for both first-variation omissions in Proposition 4.1. -/

namespace ManuscriptAudit.Paper10FirstVariationWitnesses

open ProjectedTwistedTrace
open scoped Matrix

def curvaturePath (t : ℝ) : Mat₂ := !![0, (t : ℂ); 1, 0]

noncomputable def weightedEnergy (t : ℝ) : ℝ :=
  (weightedTrace density (curvaturePath t * curvaturePath t)).re / 2

theorem weighted_energy_value (t : ℝ) : weightedEnergy t = (3 / 2) * t := by
  norm_num [weightedEnergy, weightedTrace, density, curvaturePath, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Complex.add_re, Complex.mul_re]
  <;> ring

theorem weighted_slot_values :
    (weightedTrace density (e01 * e10)).re = 2 ∧
      (weightedTrace density (e10 * e01)).re = 1 := by
  norm_num [weightedTrace, density, e01, e10, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- The weighted trace obeys twisted cyclicity, but the actual derivative
is the average of the two unequal slot values. -/
theorem twisted_trace_first_variation_witness :
    TwistedCyclic (weightedTrace density) (innerTwist density) ∧
      HasDerivAt weightedEnergy (3 / 2) 0 ∧
      ¬ HasDerivAt weightedEnergy (weightedTrace density (e01 * e10)).re 0 := by
  have h : HasDerivAt weightedEnergy (3 / 2) 0 := by
    rw [show weightedEnergy = fun t => (3 / 2) * t from funext weighted_energy_value]
    simpa only [id, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul (3 / 2 : ℝ)
  refine ⟨weightedTrace_twisted density, h, ?_⟩
  intro hh
  have hn := h.unique hh
  rw [weighted_slot_values.1] at hn
  norm_num at hn

noncomputable def scalarEnergy (a t : ℝ) : ℝ := (1 + t * a)^2 / 2

/-- Positive scalar energy with curvature variation (0+a). Dropping the
second part gives a zero variation for all directions and misses the actual value. -/
theorem omitted_braid_stationarity_witness :
    (∀ a : ℝ, (0 : ℝ) * a = 0) ∧
      (∀ a : ℝ, HasDerivAt (scalarEnergy a) a 0) ∧
      ¬ (∀ a : ℝ, HasDerivAt (scalarEnergy a) 0 0) := by
  have h (a : ℝ) : HasDerivAt (scalarEnergy a) a 0 := by
    have h0 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const _ _
    have h1 : HasDerivAt (fun t : ℝ => t * a) a 0 := by
      simpa only [id, one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const a
    have hBase : HasDerivAt (fun t : ℝ => 1 + t * a) a 0 := by
      simpa only [zero_add] using HasDerivAt.add h0 h1
    have h2 := (HasDerivAt.mul hBase hBase).div_const (2 : ℝ)
    convert h2 using 1 <;> simp [scalarEnergy, pow_two] <;> ring
  refine ⟨fun a => zero_mul a, h, ?_⟩
  intro hh
  exact one_ne_zero ((h 1).unique (hh 1))

end ManuscriptAudit.Paper10FirstVariationWitnesses

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10FirstVariationWitnesses.weighted_energy_value,
      ``ManuscriptAudit.Paper10FirstVariationWitnesses.weighted_slot_values,
      ``ManuscriptAudit.Paper10FirstVariationWitnesses.twisted_trace_first_variation_witness,
      ``ManuscriptAudit.Paper10FirstVariationWitnesses.omitted_braid_stationarity_witness] do
    let axs ← collectAxioms name
    let bad := axs.filter fun axiomName => !allowed.contains axiomName
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axs}"
