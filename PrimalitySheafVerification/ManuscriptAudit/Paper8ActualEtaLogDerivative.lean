import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-! The native fractional-linear law for the logarithmic derivative of the actual eta product. -/

namespace ManuscriptAudit.Paper8ActualEtaLogDerivative

open UpperHalfPlane EisensteinSeries ModularForm
open scoped MatrixGroups

theorem eta_logDeriv_SL2 (g : SL(2, ℤ)) (z : ℍ) :
    logDeriv ModularForm.eta ((g • z : ℍ) : ℂ) *
        ((UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z) ^ (2 : ℤ))⁻¹ =
      logDeriv ModularForm.eta z +
        (g 1 0 : ℂ) / (2 * UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z) := by
  let d := UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z
  have hd : d ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hPi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let P : ℂ := (Real.pi : ℂ) * Complex.I / 12
  let Q : ℂ := 1 / (2 * riemannZeta 2)
  have hE : E2 (g • z) * (d ^ (2 : ℤ))⁻¹ =
      E2 z - Q * (2 * (Real.pi : ℂ) * Complex.I * (g 1 0 : ℂ) / d) := by
    have h := congrFun (E2_slash_action g) z
    rw [SL_slash_def] at h
    have hD2 : D2 g z = 2 * (Real.pi : ℂ) * Complex.I * (g 1 0 : ℂ) / d := by
      unfold D2 d
      push_cast <;> ring
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zpow_neg,
      hD2, d, Q] using h
  have hExtra : -(P * (Q * (2 * (Real.pi : ℂ) * Complex.I * (g 1 0 : ℂ) / d))) =
      (g 1 0 : ℂ) / (2 * d) := by
    unfold P Q
    rw [riemannZeta_two]
    calc
      _ = -(Complex.I * Complex.I * (g 1 0 : ℂ) / (2 * d)) := by
        field_simp [hPi, hd] <;> ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  simp only [ModularForm.logDeriv_eta_eq_E2]
  change P * E2 (g • z) * (d ^ (2 : ℤ))⁻¹ = P * E2 z + (g 1 0 : ℂ) / (2 * d)
  rw [mul_assoc, hE, mul_sub, ← hExtra, sub_eq_add_neg]

end ManuscriptAudit.Paper8ActualEtaLogDerivative

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8ActualEtaLogDerivative.eta_logDeriv_SL2
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
