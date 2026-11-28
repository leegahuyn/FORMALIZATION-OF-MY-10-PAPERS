import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPentagonalExpansion
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-! Every actual eta Floquet coefficient on every horizontal line. -/

namespace ManuscriptAudit.Paper8EtaFloquetCoefficients

open Set MeasureTheory
open Function.Periodic CirclePolynomialCoefficients MaassLaplacian
open Paper8EtaPentagonalExpansion
open scoped Interval

noncomputable section

def floquetCoefficient (m : ℕ) (y : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    qParam 1 (complexPoint x y) ^ (-(m : ℤ)) *
      (ModularForm.eta (complexPoint x y) / qParam 24 (complexPoint x y))

private theorem qParam_as_circleMap (x y : ℝ) :
    qParam 1 (complexPoint x y) =
      circleMap 0 (Real.exp (-(2 * Real.pi) * y)) (x * (2 * Real.pi)) := by
  unfold qParam circleMap complexPoint
  simp only [Complex.ofReal_one, div_one, zero_add, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * (y : ℂ)) * Complex.I_sq

private theorem coefficient_interval (f : ℂ → ℂ) (m : ℕ) {R : ℝ} (hR : 0 < R) :
    coefficient f R m =
      ∫ x in (0 : ℝ)..1, circleMap 0 R (x * (2 * Real.pi)) ^ (-(m : ℤ)) *
        f (circleMap 0 R (x * (2 * Real.pi))) := by
  let Q := circleMap 0 R
  let G (θ : ℝ) := Q θ ^ (-(m : ℤ)) * f (Q θ)
  have hPoint (θ : ℝ) :
      deriv Q θ * (Q θ ^ (-(m : ℤ) - 1) * f (Q θ)) = Complex.I * G θ := by
    have hQ : Q θ ≠ 0 := by
      simp [Q, circleMap, hR.ne', Complex.exp_ne_zero]
    have hPower : Q θ * Q θ ^ (-(m : ℤ) - 1) = Q θ ^ (-(m : ℤ)) := by
      calc
        _ = Q θ ^ (1 + (-(m : ℤ) - 1)) := by rw [zpow_add₀ hQ, zpow_one]
        _ = _ := by congr 1 <;> ring
    change deriv (circleMap 0 R) θ * (Q θ ^ (-(m : ℤ) - 1) * f (Q θ)) = _
    rw [deriv_circleMap]
    change Q θ * Complex.I * (Q θ ^ (-(m : ℤ) - 1) * f (Q θ)) = _
    calc
      _ = Complex.I * ((Q θ * Q θ ^ (-(m : ℤ) - 1)) * f (Q θ)) := by ring
      _ = _ := by rw [hPower] <;> rfl
  have hI : (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv Q θ * (Q θ ^ (-(m : ℤ) - 1) * f (Q θ))) =
      Complex.I * ∫ θ in (0 : ℝ)..2 * Real.pi, G θ := by
    simp only [hPoint, intervalIntegral.integral_const_mul]
  have hScale : ((2 * Real.pi : ℝ) : ℂ) *
        (∫ x in (0 : ℝ)..1, G (x * (2 * Real.pi))) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, G θ := by
    simpa only [zero_mul, one_mul, Complex.real_smul] using
      intervalIntegral.smul_integral_comp_mul_right (a := (0 : ℝ)) (b := 1) G (2 * Real.pi)
  have hp : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (by norm_num) Real.pi_pos).ne'
  unfold coefficient circleIntegral
  simp only [smul_eq_mul]
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        deriv Q θ * (Q θ ^ (-(m : ℤ) - 1) * f (Q θ))) =
    ∫ x in (0 : ℝ)..1, G (x * (2 * Real.pi))
  rw [hI, ← hScale]
  generalize (∫ x in (0 : ℝ)..1, G (x * (2 * Real.pi))) = J
  push_cast at hp ⊢
  field_simp [hp, Complex.I_ne_zero] <;> ring

theorem floquetCoefficient_eq_pentagonal (m : ℕ) {y : ℝ} (hy : 0 < y) :
    floquetCoefficient m y = (PowerSeries.pentagonalSeries ℂ).coeff m := by
  let R := Real.exp (-(2 * Real.pi) * y)
  have hR : 0 < R := Real.exp_pos _
  have hR₁ : R < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hEta (z : ℂ) : ModularForm.eta z / qParam 24 z = etaUnit (qParam 1 z) := by
    have h : ModularForm.eta z = qParam 24 z * etaUnit (qParam 1 z) := by
      simp only [ModularForm.eta, etaUnit, ModularForm.eta_q]
    rw [h, mul_comm (qParam 24 z), mul_div_cancel_right₀ _ (qParam_ne_zero z)]
  rw [← unit_circle_coefficient hR hR₁ m, coefficient_interval etaUnit m hR]
  unfold floquetCoefficient
  simp_rw [hEta, qParam_as_circleMap] <;> rfl

theorem floquetCoefficient_at_pentagonal (k : ℤ) {y : ℝ} (hy : 0 < y) :
    floquetCoefficient (pentagonal k) y = (-1 : ℂ) ^ k.natAbs := by
  rw [floquetCoefficient_eq_pentagonal _ hy, PowerSeries.coeff_pentagonalSeries_pentagonal]
  exact Int.coe_negOnePow ℂ k

theorem floquetCoefficient_off_pentagonal {m : ℕ} {y : ℝ} (hy : 0 < y)
    (hm : m ∉ Set.range pentagonal) : floquetCoefficient m y = 0 := by
  rw [floquetCoefficient_eq_pentagonal _ hy, PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hm]

end
end ManuscriptAudit.Paper8EtaFloquetCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaFloquetCoefficients.floquetCoefficient_eq_pentagonal,
      ``ManuscriptAudit.Paper8EtaFloquetCoefficients.floquetCoefficient_at_pentagonal,
      ``ManuscriptAudit.Paper8EtaFloquetCoefficients.floquetCoefficient_off_pentagonal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
