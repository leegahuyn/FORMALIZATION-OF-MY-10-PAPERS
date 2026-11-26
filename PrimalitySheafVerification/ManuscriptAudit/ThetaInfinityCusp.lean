import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-!
# The Jacobi theta mode on the infinity cusp strip

Paper 9 uses the width-two cusp strip and the hyperbolic density
`y⁻² dx dy` on physical PDF pp. 402 and 409. This proof treats the same
actual weighted Jacobi theta as the pointwise Maass equation. The domain
is the coordinate strip above a specified positive height.
-/

namespace ManuscriptAudit.ThetaInfinityCusp

open MaassLaplacian MeasureTheory Set
open scoped ENNReal

noncomputable section

def infinityStripAbove (H : ℝ) : Set (ℝ × ℝ) := Ioc 0 2 ×ˢ Ioi H

abbrev infinityStrip : Set (ℝ × ℝ) := infinityStripAbove 1

private def cuspDensity (z : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.2 ^ 2)⁻¹)

/-- Hyperbolic area on the width-two strip, in real coordinates. -/
def infinityCuspMeasureAbove (H : ℝ) : Measure (ℝ × ℝ) :=
  (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (infinityStripAbove H)).withDensity
    cuspDensity

abbrev infinityCuspMeasure : Measure (ℝ × ℝ) := infinityCuspMeasureAbove 1

private def thetaBound (H : ℝ) : ℝ := 2 / (1 - Real.exp (-Real.pi * H)) + 1

private theorem norm_theta_le {H x y : ℝ} (hH : 0 < H) (hy : H ≤ y) :
    ‖jacobiTheta (complexPoint x y)‖ ≤ thetaBound H := by
  let q := Real.exp (-Real.pi * y)
  let q₁ := Real.exp (-Real.pi * H)
  have hq : q ≤ q₁ :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hy (neg_nonpos.mpr Real.pi_pos.le))
  have hq₁ : q₁ < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hH)
  have hd₁ : 0 < 1 - q₁ := sub_pos.mpr hq₁
  have hd : 1 - q₁ ≤ 1 - q := sub_le_sub_left hq 1
  have hy' : 0 < (complexPoint x y).im := by
    rw [complexPoint_im]
    exact hH.trans_le hy
  have hDiff := norm_jacobiTheta_sub_one_le hy'
  rw [complexPoint_im] at hDiff
  change ‖jacobiTheta (complexPoint x y) - 1‖ ≤ 2 / (1 - q) * q at hDiff
  have hFrac : 2 / (1 - q) * q ≤ 2 / (1 - q₁) := by
    calc
      _ ≤ 2 / (1 - q) * 1 :=
        mul_le_mul_of_nonneg_left (hq.trans hq₁.le)
          (div_nonneg (by norm_num) (hd₁.le.trans hd))
      _ = 2 / (1 - q) := mul_one _
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hd₁ hd
  calc
    ‖jacobiTheta (complexPoint x y)‖ = ‖(jacobiTheta (complexPoint x y) - 1) + 1‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖jacobiTheta (complexPoint x y) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ thetaBound H := by
      change _ ≤ 2 / (1 - q₁) + 1
      rw [norm_one]
      exact add_le_add (hDiff.trans hFrac) le_rfl

private theorem sq_mul_density (f : ℂ → ℂ) (a x y : ℝ) (hy : 0 < y) :
    (y ^ 2)⁻¹ * ‖weighted a f x y‖ ^ 2 =
      ‖f (complexPoint x y)‖ ^ 2 * y ^ (a * 2 - 2) := by
  change (y ^ 2)⁻¹ * ‖((y ^ a : ℝ) : ℂ) * f (complexPoint x y)‖ ^ 2 = _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy.le a),
    mul_pow, Real.rpow_sub hy, Real.rpow_two y, Real.rpow_mul hy.le a 2,
    Real.rpow_two (y ^ a), div_eq_mul_inv]
  ring

/-- A bounded continuous holomorphic-coordinate profile gives a square-integrable
mode after any height weighting with exponent less than one half. -/
theorem weighted_memLp_of_bound (f : ℂ → ℂ) (H a B : ℝ) (hH : 0 < H) (ha : a < 1 / 2)
    (hContinuous : ∀ τ, 0 < τ.im → ContinuousAt f τ)
    (hBound : ∀ x y, H ≤ y → ‖f (complexPoint x y)‖ ≤ B) :
    MemLp (fun z : ℝ × ℝ => weighted a f z.1 z.2) 2 (infinityCuspMeasureAbove H) := by
  let μ : Measure (ℝ × ℝ) := ((volume : Measure ℝ).prod volume).restrict (infinityStripAbove H)
  let F (z : ℝ × ℝ) : ℂ := weighted a f z.1 z.2
  let height (z : ℝ × ℝ) : ℝ := max H z.2
  let G (z : ℝ × ℝ) : ℂ := weighted a f z.1 (height z)
  have hStrip : MeasurableSet (infinityStripAbove H) := measurableSet_Ioc.prod measurableSet_Ioi
  have hAE : ∀ᵐ z ∂μ, z ∈ infinityStripAbove H := self_mem_ae_restrict hStrip
  have hHeight : Continuous height := continuous_const.max continuous_snd
  have hHeightPos (z : ℝ × ℝ) : 0 < height z := hH.trans_le (le_max_left _ _)
  have hPoint : Continuous (fun z : ℝ × ℝ => complexPoint z.1 (height z)) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp hHeight).mul continuous_const)
  have hG : Continuous G := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    have hWeight : ContinuousAt (fun w : ℝ × ℝ => height w ^ a) z :=
      (Real.continuousAt_rpow_const (height z) a (Or.inl (hHeightPos z).ne')).comp
        hHeight.continuousAt
    have hTheta : ContinuousAt f (complexPoint z.1 (height z)) :=
      hContinuous _ (by simpa only [complexPoint_im] using hHeightPos z)
    have hThetaAt : ContinuousAt (fun w : ℝ × ℝ => f (complexPoint w.1 (height w))) z :=
      ContinuousAt.comp' (f := fun w : ℝ × ℝ => complexPoint w.1 (height w)) (x := z)
        hTheta hPoint.continuousAt
    exact (Complex.continuous_ofReal.continuousAt.comp hWeight).mul hThetaAt
  have hEq : G =ᵐ[μ] F := hAE.mono fun z hz => by
    have hy : H < z.2 := hz.2
    simp only [G, F, height, max_eq_right hy.le]
  have hMeas : AEStronglyMeasurable F μ := hG.aestronglyMeasurable.congr hEq
  have hDensity : Measurable cuspDensity := ((measurable_snd.pow_const 2).inv).ennreal_ofReal
  have hPower : IntegrableOn (fun y : ℝ => y ^ (a * 2 - 2)) (Ioi H) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hH
  have hMajor : Integrable (fun z : ℝ × ℝ => B ^ 2 * z.2 ^ (a * 2 - 2)) μ := by
    dsimp only [μ, infinityStripAbove]
    rw [← Measure.prod_restrict]
    exact (hPower.const_mul (B ^ 2)).comp_snd
      ((volume : Measure ℝ).restrict (Ioc 0 2))
  change MemLp F 2 (μ.withDensity cuspDensity)
  apply (memLp_two_iff_integrable_sq_norm
    (AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous μ cuspDensity) hMeas)).2
  apply (integrable_withDensity_iff_integrable_smul' hDensity
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  have hProduct : AEStronglyMeasurable (fun z => (cuspDensity z).toReal • ‖F z‖ ^ 2) μ := by
    change AEStronglyMeasurable
      ((fun z : ℝ × ℝ => (cuspDensity z).toReal) * (fun z : ℝ × ℝ => ‖F z‖) ^ 2) μ
    exact hDensity.ennreal_toReal.aestronglyMeasurable.mul (hMeas.norm.pow 2)
  apply Integrable.mono' hMajor hProduct
  filter_upwards [hAE] with z hz
  have hy : H < z.2 := hz.2
  have hy' : 0 < z.2 := hH.trans hy
  have hInv : 0 ≤ (z.2 ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  change ‖(cuspDensity z).toReal • ‖F z‖ ^ 2‖ ≤ B ^ 2 * z.2 ^ (a * 2 - 2)
  rw [cuspDensity, ENNReal.toReal_ofReal hInv, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hInv (sq_nonneg _))]
  change (z.2 ^ 2)⁻¹ * ‖weighted a f z.1 z.2‖ ^ 2 ≤ _
  rw [sq_mul_density f a z.1 z.2 hy']
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hBound z.1 z.2 hy.le) 2)
    (Real.rpow_nonneg hy'.le _)

/-- The native Jacobi theta mode belongs to L² on the strip. -/
theorem weighted_jacobiTheta_memLp_infinity_above (H a : ℝ) (hH : 0 < H) (ha : a < 1 / 2) :
    MemLp (fun z : ℝ × ℝ => weighted a jacobiTheta z.1 z.2) 2 (infinityCuspMeasureAbove H) := by
  refine weighted_memLp_of_bound jacobiTheta H a (thetaBound H) hH ha ?_ ?_
  · intro τ hτ
    exact (differentiableAt_jacobiTheta (τ := τ) hτ).continuousAt
  · intro x y hy
    exact norm_theta_le hH hy

/-- The same square-integrability statement above height one. -/
theorem weighted_jacobiTheta_memLp_infinity (a : ℝ) (ha : a < 1 / 2) :
    MemLp (fun z : ℝ × ℝ => weighted a jacobiTheta z.1 z.2) 2 infinityCuspMeasure :=
  weighted_jacobiTheta_memLp_infinity_above 1 a zero_lt_one ha

/-- The quarter-height Jacobi theta mode from the pointwise weight-one-half
Maass equation is L² on this width-two infinity cusp strip. -/
theorem jacobiTheta_half_memLp_infinity :
    MemLp (fun z : ℝ × ℝ => weighted (1 / 4) jacobiTheta z.1 z.2) 2 infinityCuspMeasure :=
  weighted_jacobiTheta_memLp_infinity (1 / 4) (by norm_num)

end

end ManuscriptAudit.ThetaInfinityCusp

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ThetaInfinityCusp.weighted_memLp_of_bound,
      ``ManuscriptAudit.ThetaInfinityCusp.weighted_jacobiTheta_memLp_infinity_above,
      ``ManuscriptAudit.ThetaInfinityCusp.weighted_jacobiTheta_memLp_infinity,
      ``ManuscriptAudit.ThetaInfinityCusp.jacobiTheta_half_memLp_infinity] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
