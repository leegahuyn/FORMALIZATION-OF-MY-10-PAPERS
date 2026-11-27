import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaRatioCuspLimit

/-! Polynomial growth of a normalized half-weight translate is enough for eta-ratio removability. -/

namespace ManuscriptAudit.Paper8EtaRatioPolynomialGrowth

open Set Filter Function UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8ActualEtaNormCusp Paper8EtaRatioCuspLimit
open scoped MatrixGroups Manifold Topology

theorem height_rpow_mul_q_rpow_tendsto_zero {w d : ℝ} (hw : 0 < w) (hd : 0 < d) (p : ℝ) :
    Tendsto (fun z : ℍ => z.im ^ p * ‖Periodic.qParam w z‖ ^ d) atImInfty (𝓝 0) := by
  let b : ℝ := 2 * Real.pi * d / w
  have hb : 0 < b := by unfold b; positivity
  have hIm : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p b hb).comp hIm
  refine h.congr (fun z => ?_)
  simp only [Function.comp_apply, Periodic.norm_qParam, ← Real.exp_mul]
  congr 2
  unfold b
  ring

theorem eta_ratio_subPole_growth_of_polynomial {f : ℍ → ℂ} (g : SL(2, ℤ))
    {w : ℕ} (hw : 0 < w) {p M beta : ℝ} (hM : 0 ≤ M) (hBeta : (w : ℝ) / 24 < beta)
    (hBound : ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z)‖ ≤ (M * z.im ^ p) * Real.sqrt ‖denominator g z‖) :
    ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z) / ModularForm.eta (g • z : ℍ)‖ ≤ (2 * M) / ‖Periodic.qParam (w : ℝ) z‖ ^ beta := by
  let alpha : ℝ := (w : ℝ) / 24
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hT := height_rpow_mul_q_rpow_tendsto_zero hwR (sub_pos.mpr hBeta) p
  filter_upwards [hBound, eta_eventual_lower_bound hw, hT.eventually
    (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with z hz hEtaBound hSmall
  let q : ℝ := ‖Periodic.qParam (w : ℝ) z‖
  let d : ℝ := Real.sqrt ‖denominator g z‖
  let e : ℝ := ‖ModularForm.eta z‖
  let B : ℝ := z.im ^ p
  have hq : 0 < q := norm_pos_iff.mpr (Periodic.qParam_ne_zero _)
  have hqa : 0 < q ^ alpha := Real.rpow_pos_of_pos hq _
  have hqb : 0 < q ^ beta := Real.rpow_pos_of_pos hq _
  have hd : 0 < d := Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))
  have he : 0 < e := norm_pos_iff.mpr (ModularForm.eta_ne_zero z.im_pos)
  have hB : 0 ≤ B := Real.rpow_nonneg z.im_pos.le _
  have hSmall' : B * q ^ (beta - alpha) ≤ 1 := hSmall.le
  have hEtaBound' : (1 / 2 : ℝ) * q ^ alpha ≤ e := hEtaBound
  have hEtaCompare : M * B / e ≤ (2 * M) * (B / q ^ alpha) := by
    rw [← mul_div_assoc, div_le_div_iff₀ he hqa]
    nlinarith [mul_le_mul_of_nonneg_left hEtaBound' (mul_nonneg hM hB)]
  have hWeights : B / q ^ alpha ≤ 1 / q ^ beta := by
    have hAdd : q ^ beta = q ^ alpha * q ^ (beta - alpha) := by
      rw [← Real.rpow_add hq]
      exact congrArg (fun x : ℝ => q ^ x) (by ring : beta = alpha + (beta - alpha))
    rw [div_le_div_iff₀ hqa hqb, one_mul, hAdd]
    calc
      _ = q ^ alpha * (B * q ^ (beta - alpha)) := by ring
      _ ≤ q ^ alpha := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hSmall' hqa.le
  rw [norm_div, eta_norm_transform]
  change ‖f (g • z)‖ / (d * e) ≤ (2 * M) / q ^ beta
  calc
    _ ≤ ((M * B) * d) / (d * e) := div_le_div_of_nonneg_right hz (mul_nonneg hd.le he.le)
    _ = M * B / e := by field_simp [hd.ne', he.ne'] <;> ring
    _ ≤ (2 * M) * (B / q ^ alpha) := hEtaCompare
    _ ≤ (2 * M) * (1 / q ^ beta) := mul_le_mul_of_nonneg_left hWeights (by positivity)
    _ = _ := by rw [← mul_div_assoc, mul_one]

theorem eta_ratio_limit_of_polynomial_growth {f : ℍ → ℂ} (g : SL(2, ℤ)) {w : ℕ}
    (hw : 0 < w) (hw24 : w < 24) {p M : ℝ} (hM : 0 ≤ M)
    (hPer : Periodic ((fun z : ℍ => f (g • z) / ModularForm.eta (g • z : ℍ)) ∘ ofComplex) (w : ℝ))
    (hHol : MDiff (fun z : ℍ => f (g • z) / ModularForm.eta (g • z : ℍ)))
    (hBound : ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z)‖ ≤ (M * z.im ^ p) * Real.sqrt ‖denominator g z‖) :
    ∃ L : ℂ, Tendsto (fun z : ℍ => f (g • z) / ModularForm.eta (g • z : ℍ)) atImInfty (𝓝 L) := by
  let beta : ℝ := ((w : ℝ) / 24 + 1) / 2
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hwR24 : (w : ℝ) < 24 := by exact_mod_cast hw24
  have hBeta : (w : ℝ) / 24 < beta := by unfold beta; linarith
  have hBeta1 : beta < 1 := by unfold beta; linarith
  exact exists_limit_of_subPoleGrowth hwR hPer hBeta1 hHol
    (eta_ratio_subPole_growth_of_polynomial g hw hM hBeta hBound)

end ManuscriptAudit.Paper8EtaRatioPolynomialGrowth

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaRatioPolynomialGrowth.height_rpow_mul_q_rpow_tendsto_zero,
      ``ManuscriptAudit.Paper8EtaRatioPolynomialGrowth.eta_ratio_subPole_growth_of_polynomial,
      ``ManuscriptAudit.Paper8EtaRatioPolynomialGrowth.eta_ratio_limit_of_polynomial_growth] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
