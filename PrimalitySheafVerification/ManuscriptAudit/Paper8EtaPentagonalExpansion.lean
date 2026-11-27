import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.NumberTheory.ModularForms.DedekindEta
import PrimalitySheafVerification.ManuscriptAudit.CirclePolynomialCoefficients

/-! Actual complex eta coefficients from the formal Euler pentagonal theorem. -/

namespace ManuscriptAudit.Paper8EtaPentagonalExpansion

open Filter Function.Periodic Metric Set
open CirclePolynomialCoefficients
open scoped Topology NNReal ENNReal

noncomputable section

def etaUnit (q : ℂ) : ℂ := ∏' j : ℕ, (1 - q ^ (j + 1))

private def partialPolynomial (n : ℕ) : Polynomial ℂ :=
  ∏ j ∈ Finset.range n, (1 - Polynomial.X ^ (j + 1))

private theorem partialPolynomial_eval (n : ℕ) (q : ℂ) :
    (partialPolynomial n).eval q = ∏ j ∈ Finset.range n, (1 - q ^ (j + 1)) := by
  change (Polynomial.evalRingHom q) (partialPolynomial n) = _
  simp [partialPolynomial, map_prod]

private theorem partialPolynomial_coeff_eventually (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, (partialPolynomial n).coeff m = (PowerSeries.pentagonalSeries ℂ).coeff m := by
  have h := Filter.tendsto_finset_range.eventually
    (PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℂ m)
  filter_upwards [h] with n hn
  have hCast : (↑(partialPolynomial n) : PowerSeries ℂ) =
      ∏ j ∈ Finset.range n, (1 - PowerSeries.X ^ (j + 1)) := by
    change Polynomial.coeToPowerSeries.ringHom (partialPolynomial n) = _
    simp [partialPolynomial, map_prod, Polynomial.coeToPowerSeries.ringHom_apply]
  rw [← Polynomial.coeff_coe, hCast]
  exact hn

theorem unit_circle_coefficient {R : ℝ} (hR : 0 < R) (hR₁ : R < 1) (m : ℕ) :
    coefficient etaUnit R m = (PowerSeries.pentagonalSeries ℂ).coeff m := by
  have hSphere : sphere (0 : ℂ) R ⊆ ball 0 1 := by
    intro q hq
    rw [mem_ball, mem_sphere.mp hq]
    exact hR₁
  have hP := (ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.mono
    hSphere).hasProdUniformlyOn_of_isCompact (isCompact_sphere (0 : ℂ) R)
  have hUniform : TendstoUniformlyOn (fun n : ℕ => (partialPolynomial n).eval)
      etaUnit atTop (sphere (0 : ℂ) R) := by
    simpa only [partialPolynomial_eval, etaUnit] using hP.tendstoUniformlyOn_finsetRange
  have hC (n : ℕ) : ContinuousOn (partialPolynomial n).eval (sphere (0 : ℂ) R) :=
    fun _ _ => (partialPolynomial n).differentiableAt.continuousAt.continuousWithinAt
  have hT := coefficient_tendsto_uniformly hR m hC hUniform
  have hA : Tendsto (fun n : ℕ => coefficient (partialPolynomial n).eval R m) atTop
      (𝓝 ((PowerSeries.pentagonalSeries ℂ).coeff m)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [partialPolynomial_coeff_eventually m] with n hn
    rw [coefficient_polynomial_eval _ hR, hn]
  exact tendsto_nhds_unique hT hA

private theorem cauchy_apply_eq_coefficient (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (m : ℕ) (q : ℂ) :
    cauchyPowerSeries f 0 R m (fun _ => q) = coefficient f R m * q ^ m := by
  have hEq : Set.EqOn (fun z : ℂ => (q / z) ^ m * (z⁻¹ * f z))
      (fun z => q ^ m * (z ^ (-(m : ℤ) - 1) * f z)) (sphere (0 : ℂ) R) := by
    intro z _
    have hzpow : (z⁻¹ : ℂ) ^ m * z⁻¹ = z ^ (-(m : ℤ) - 1) := by
      rw [← pow_succ, ← zpow_natCast, inv_zpow, ← zpow_neg, Int.natCast_succ]
      congr 1 <;> ring
    rw [div_eq_mul_inv, mul_pow]
    calc
      q ^ m * (z⁻¹ ^ m) * (z⁻¹ * f z) = q ^ m * (((z⁻¹) ^ m * z⁻¹) * f z) := by ring
      _ = _ := by rw [hzpow]
  rw [cauchyPowerSeries_apply]
  simp only [sub_zero, smul_eq_mul]
  rw [circleIntegral.integral_congr hR.le hEq, circleIntegral.integral_const_mul]
  unfold coefficient
  ring

/-- The signed pentagonal coefficient series converges to the actual analytic Euler product. -/
theorem hasSum_etaUnit (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => (PowerSeries.pentagonalSeries ℂ).coeff m * q ^ m) (etaUnit q) := by
  let R : ℝ≥0 := ⟨(‖q‖ + 1) / 2, by positivity⟩
  have hR₀ : 0 < (R : ℝ) := by
    change 0 < (‖q‖ + 1) / 2
    positivity
  have hR₁ : (R : ℝ) < 1 := by
    change (‖q‖ + 1) / 2 < 1
    linarith
  have hqR : ‖q‖ < (R : ℝ) := by
    change ‖q‖ < (‖q‖ + 1) / 2
    linarith
  have hSub : closedBall (0 : ℂ) (R : ℝ) ⊆ ball 0 1 := by
    intro z hz
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hR₁)
  have hDif : DifferentiableOn ℂ etaUnit (closedBall (0 : ℂ) R) :=
    ModularForm.differentiableOn_tprod_one_sub_pow.mono hSub
  have hSeries := hDif.hasFPowerSeriesOnBall (show 0 < R from hR₀)
  have hqE : q ∈ Metric.eball (0 : ℂ) (R : ℝ≥0∞) := by
    rw [Metric.eball_coe]
    simpa only [Metric.mem_ball, dist_zero_right] using hqR
  simpa only [cauchy_apply_eq_coefficient etaUnit hR₀, unit_circle_coefficient hR₀ hR₁,
    zero_add] using hSeries.hasSum hqE

/-- At a genuine upper-half-plane point, the full native eta series has the
signed formal pentagonal coefficients in its integer-shifted cusp powers. -/
theorem hasSum_eta (z : UpperHalfPlane) :
    HasSum (fun m : ℕ => qParam 24 z * ((PowerSeries.pentagonalSeries ℂ).coeff m *
      qParam 1 z ^ m)) (ModularForm.eta z) := by
  have hq : ‖qParam 1 z‖ < 1 := by
    simpa only [Nat.cast_one] using UpperHalfPlane.norm_qParam_lt_one 1 z
  have h := (hasSum_etaUnit (qParam 1 z) hq).mul_left (qParam 24 z)
  simpa [etaUnit, ModularForm.eta, ModularForm.eta_q] using h

end
end ManuscriptAudit.Paper8EtaPentagonalExpansion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaPentagonalExpansion.unit_circle_coefficient,
      ``ManuscriptAudit.Paper8EtaPentagonalExpansion.hasSum_etaUnit,
      ``ManuscriptAudit.Paper8EtaPentagonalExpansion.hasSum_eta] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
