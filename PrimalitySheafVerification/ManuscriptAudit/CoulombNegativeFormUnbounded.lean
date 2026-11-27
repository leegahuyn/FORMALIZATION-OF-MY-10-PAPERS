import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombScaledCuspIntegrals
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspLaplacianTest

/-! The literal negative covariant-derivative form is unbounded below relative to cusp mass. -/

namespace ManuscriptAudit.CoulombNegativeFormUnbounded

open MeasureTheory Set HyperbolicCuspGaugeTest CoulombScaledCuspForms CoulombScaledCuspIntegrals

noncomputable section

private theorem pulled_energy_point_lower (r t : ℝ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (r ^ 2 / 2) * deriv cuspBump t ^ 2 ≤ pulledEnergy r t := by
  have hy : r ≤ t - shift r := by unfold shift; linarith
  have hs : r ^ 2 ≤ (t - shift r) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hy 2
  have hQ := mul_le_mul_of_nonneg_right hs (sq_nonneg (deriv cuspBump t))
  have hS := sq_nonneg ((t - shift r) * deriv cuspBump t + 2 * cuspBump t)
  unfold pulledEnergy
  nlinarith only [hQ, hS]

theorem energy_lower (r : ℝ) (hr : 1 ≤ r) :
    r * (∫ t : ℝ in (1 : ℝ)..6, deriv cuspBump t ^ 2) ≤ energy r := by
  have hr₀ : 0 < r := by linarith
  have hb := cuspBump_smooth.continuous
  have hc : Continuous (pulledEnergy r) :=
    (hb.pow 2).add ((((continuous_id.sub continuous_const).mul bump_deriv_continuous).add hb).pow 2)
  have hL : Continuous (fun t => (r ^ 2 / 2) * deriv cuspBump t ^ 2) :=
    continuous_const.mul (bump_deriv_continuous.pow 2)
  have hi : (∫ t : ℝ in (1 : ℝ)..6, (r ^ 2 / 2) * deriv cuspBump t ^ 2) ≤
      ∫ t : ℝ in (1 : ℝ)..6, pulledEnergy r t := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hL.intervalIntegrable 1 6) (hc.intervalIntegrable 1 6)
    exact fun t ht => pulled_energy_point_lower r t hr ht.1
  rw [intervalIntegral.integral_const_mul] at hi
  have h := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * r⁻¹ by positivity)
  rw [← energy_rescaled r hr] at h
  have hs (x : ℝ) : (2 * r⁻¹) * (r ^ 2 / 2 * x) = r * x := by
    field_simp [hr₀.ne'] <;> ring
  rwa [hs] at h

theorem negative_form_no_mass_lower_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ r : ℝ, 1 ≤ r ∧ 0 < mass r ∧ -energy r < -C * mass r := by
  let U := ∫ t : ℝ in (1 : ℝ)..6, cuspBump t ^ 2
  let D := ∫ t : ℝ in (1 : ℝ)..6, deriv cuspBump t ^ 2
  have hU : 0 < U := by
    have h := cuspMass_pos
    change 0 < 2 * U at h
    linarith
  have hD : 0 < D := Paper9CuspLaplacianTest.derivative_square_integral_pos
  let r := 2 + 2 * C * U / D
  have hR : 2 ≤ r := le_add_of_nonneg_right (by positivity)
  have hr : 1 ≤ r := by linarith
  have hr₀ : 0 < r := by linarith
  have hm : mass r = (2 * r⁻¹) * U := mass_rescaled r hr
  refine ⟨r, hr, by rw [hm]; positivity, ?_⟩
  have hRD : r * D = 2 * D + 2 * C * U := by
    dsimp [r]
    field_simp [hD.ne'] <;> ring
  have hR₂ : r ≤ r ^ 2 := by
    nlinarith [mul_nonneg hr₀.le (show 0 ≤ r - 1 by linarith)]
  have hLarge : 2 * C * U < r ^ 2 * D := by
    calc
      _ < r * D := by rw [hRD]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hR₂ hD.le
  have hComparison : C * mass r < r * D := by
    rw [hm, show C * (2 * r⁻¹ * U) = (2 * C * U) / r by rw [div_eq_mul_inv]; ring]
    apply (div_lt_iff₀ hr₀).mpr
    convert hLarge using 1 <;> ring
  have hE : r * D ≤ energy r := energy_lower r hr
  nlinarith only [hComparison.trans_le hE]

end
end ManuscriptAudit.CoulombNegativeFormUnbounded

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombNegativeFormUnbounded.energy_lower,
      ``ManuscriptAudit.CoulombNegativeFormUnbounded.negative_form_no_mass_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
