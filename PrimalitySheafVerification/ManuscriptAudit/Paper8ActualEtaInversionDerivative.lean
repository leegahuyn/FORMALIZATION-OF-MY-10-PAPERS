import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.Tactic.LinearCombination

/-!
# The actual eta logarithmic derivative under inversion

The native logarithmic derivative of eta and the native weight-two
Eisenstein inversion identity give the exact additional 1/(2z) term.
-/

namespace ManuscriptAudit.Paper8ActualEtaInversionDerivative

open UpperHalfPlane EisensteinSeries

theorem eta_logDeriv_inversion (z : ℍ) :
    logDeriv ModularForm.eta ((ModularGroup.S • z : ℍ) : ℂ) * (((z : ℂ) ^ 2)⁻¹) =
      logDeriv ModularForm.eta z + 1 / (2 * (z : ℂ)) := by
  have hG : (((z : ℂ) ^ 2)⁻¹) * G2 (ModularGroup.S • z) =
      G2 z + (-2 : ℂ) * (Real.pi : ℂ) * Complex.I / (z : ℂ) := by
    linear_combination -(G2_S_transform z)
  let A : ℂ := (Real.pi : ℂ) * Complex.I / 12 * (1 / (2 * riemannZeta 2))
  have hPi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hExtra : A * ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I / (z : ℂ)) =
      1 / (2 * (z : ℂ)) := by
    unfold A
    rw [riemannZeta_two]
    calc
      _ = -(Complex.I * Complex.I / (2 * (z : ℂ))) := by
        field_simp [hPi, z.ne_zero] <;> ring
      _ = _ := by rw [Complex.I_mul_I, neg_div, neg_neg]
  simp only [ModularForm.logDeriv_eta_eq_E2, E2, Pi.smul_apply, smul_eq_mul]
  calc
    _ = A * (((z : ℂ) ^ 2)⁻¹ * G2 (ModularGroup.S • z)) := by unfold A; ring
    _ = A * G2 z + 1 / (2 * (z : ℂ)) := by rw [hG, mul_add, hExtra]
    _ = _ := by unfold A; ring

end ManuscriptAudit.Paper8ActualEtaInversionDerivative

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8ActualEtaInversionDerivative.eta_logDeriv_inversion
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
