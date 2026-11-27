import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# The actual Dedekind eta translation phase

Mathlib's native Dedekind eta function has the phase exp(2πi m/24) under
translation by any integer m. This establishes the width-one phase at
infinity directly from its infinite product.
-/

namespace ManuscriptAudit.Paper8ActualEtaTranslation

open Function.Periodic

theorem eta_add_integer (z : ℂ) (m : ℤ) :
    ModularForm.eta (z + (m : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / 24) * ModularForm.eta z := by
  have hExp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) = 1 := by
    rw [mul_comm, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  have hOne : qParam 1 (z + (m : ℂ)) = qParam 1 z := by
    unfold qParam
    simp only [Complex.ofReal_one, div_one, mul_add, Complex.exp_add, hExp, mul_one]
  have hWidth : qParam 24 (z + (m : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / 24) * qParam 24 z := by
    unfold qParam
    rw [mul_add, add_div, Complex.exp_add, mul_comm] <;> norm_num
  unfold ModularForm.eta
  rw [hWidth]
  simp only [ModularForm.eta_q, hOne, mul_assoc]

theorem eta_width_one_shifted_frequency :
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((23 / 24 : ℝ) : ℂ))) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 24) := by
  have hArg : -(2 * (Real.pi : ℂ) * Complex.I * ((23 / 24 : ℝ) : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I / 24 - (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hArg, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]

end ManuscriptAudit.Paper8ActualEtaTranslation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaTranslation.eta_add_integer,
      ``ManuscriptAudit.Paper8ActualEtaTranslation.eta_width_one_shifted_frequency] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
