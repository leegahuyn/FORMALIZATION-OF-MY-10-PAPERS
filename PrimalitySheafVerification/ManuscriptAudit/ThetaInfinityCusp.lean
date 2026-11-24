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
is the coordinate strip above height one.
-/

namespace ManuscriptAudit.ThetaInfinityCusp

open MaassLaplacian MeasureTheory Set
open scoped ENNReal

noncomputable section

def infinityStrip : Set (ℝ × ℝ) := Ioc 0 2 ×ˢ Ioi 1

private def cuspDensity (z : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.2 ^ 2)⁻¹)

/-- Hyperbolic area on the width-two strip, in real coordinates. -/
def infinityCuspMeasure : Measure (ℝ × ℝ) :=
  (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict infinityStrip).withDensity
    cuspDensity

private def thetaBound : ℝ := 2 / (1 - Real.exp (-Real.pi)) + 1

private theorem norm_theta_le {x y : ℝ} (hy : 1 ≤ y) :
    ‖jacobiTheta (complexPoint x y)‖ ≤ thetaBound := by
  let q := Real.exp (-Real.pi * y)
  let q₁ := Real.exp (-Real.pi)
  have hq : q ≤ q₁ := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_one] using mul_le_mul_of_nonpos_left hy (neg_nonpos.mpr Real.pi_pos.le)
  have hq₁ : q₁ < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)
  have hd₁ : 0 < 1 - q₁ := sub_pos.mpr hq₁
  have hd : 1 - q₁ ≤ 1 - q := sub_le_sub_left hq 1
  have hy' : 0 < (complexPoint x y).im := by
    rw [complexPoint_im]
    exact zero_lt_one.trans_le hy
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
    _ ≤ thetaBound := by
      change _ ≤ 2 / (1 - q₁) + 1
      rw [norm_one]
      exact add_le_add (hDiff.trans hFrac) le_rfl

private theorem sq_mul_density (a x y : ℝ) (hy : 0 < y) :
    (y ^ 2)⁻¹ * ‖weighted a jacobiTheta x y‖ ^ 2 =
      ‖jacobiTheta (complexPoint x y)‖ ^ 2 * y ^ (a * 2 - 2) := by
  change (y ^ 2)⁻¹ * ‖((y ^ a : ℝ) : ℂ) * jacobiTheta (complexPoint x y)‖ ^ 2 = _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy.le a),
    mul_pow, Real.rpow_sub hy, Real.rpow_two y, Real.rpow_mul hy.le a 2,
    Real.rpow_two (y ^ a), div_eq_mul_inv]
  ring

/-- The actual Jacobi theta mode at height power a belongs to L² on the
infinity strip when the local exponent satisfies a < 1/2. -/
theorem weighted_jacobiTheta_memLp_infinity (a : ℝ) (ha : a < 1 / 2) :
    MemLp (fun z : ℝ × ℝ => weighted a jacobiTheta z.1 z.2) 2 infinityCuspMeasure := by
  let μ : Measure (ℝ × ℝ) := ((volume : Measure ℝ).prod volume).restrict infinityStrip
  let F (z : ℝ × ℝ) : ℂ := weighted a jacobiTheta z.1 z.2
  let height (z : ℝ × ℝ) : ℝ := max 1 z.2
  let G (z : ℝ × ℝ) : ℂ := weighted a jacobiTheta z.1 (height z)
  have hStrip : MeasurableSet infinityStrip := measurableSet_Ioc.prod measurableSet_Ioi
  have hAE : ∀ᵐ z ∂μ, z ∈ infinityStrip := self_mem_ae_restrict hStrip
  have hHeight : Continuous height := continuous_const.max continuous_snd
  have hHeightPos (z : ℝ × ℝ) : 0 < height z := zero_lt_one.trans_le (le_max_left _ _)
  have hPoint : Continuous (fun z : ℝ × ℝ => complexPoint z.1 (height z)) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp hHeight).mul continuous_const)
  have hG : Continuous G := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    have hWeight : ContinuousAt (fun w : ℝ × ℝ => height w ^ a) z :=
      (Real.continuousAt_rpow_const (height z) a (Or.inl (hHeightPos z).ne')).comp
        hHeight.continuousAt
    have hTheta : ContinuousAt jacobiTheta (complexPoint z.1 (height z)) :=
      (differentiableAt_jacobiTheta (τ := complexPoint z.1 (height z))
        (by simpa only [complexPoint_im] using hHeightPos z)).continuousAt
    have hThetaAt : ContinuousAt (fun w : ℝ × ℝ => jacobiTheta (complexPoint w.1 (height w))) z :=
      ContinuousAt.comp' (f := fun w : ℝ × ℝ => complexPoint w.1 (height w)) (x := z)
        hTheta hPoint.continuousAt
    exact (Complex.continuous_ofReal.continuousAt.comp hWeight).mul hThetaAt
  have hEq : G =ᵐ[μ] F := hAE.mono fun z hz => by
    have hy : 1 < z.2 := hz.2
    simp only [G, F, height, max_eq_right hy.le]
  have hMeas : AEStronglyMeasurable F μ := hG.aestronglyMeasurable.congr hEq
  have hDensity : Measurable cuspDensity := ((measurable_snd.pow_const 2).inv).ennreal_ofReal
  have hPower : IntegrableOn (fun y : ℝ => y ^ (a * 2 - 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hMajor : Integrable (fun z : ℝ × ℝ => thetaBound ^ 2 * z.2 ^ (a * 2 - 2)) μ := by
    dsimp only [μ, infinityStrip]
    rw [← Measure.prod_restrict]
    exact (hPower.const_mul (thetaBound ^ 2)).comp_snd
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
  have hy : 1 < z.2 := hz.2
  have hy' : 0 < z.2 := zero_lt_one.trans hy
  have hInv : 0 ≤ (z.2 ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  change ‖(cuspDensity z).toReal • ‖F z‖ ^ 2‖ ≤ thetaBound ^ 2 * z.2 ^ (a * 2 - 2)
  rw [cuspDensity, ENNReal.toReal_ofReal hInv, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hInv (sq_nonneg _))]
  change (z.2 ^ 2)⁻¹ * ‖weighted a jacobiTheta z.1 z.2‖ ^ 2 ≤ _
  rw [sq_mul_density a z.1 z.2 hy']
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (norm_theta_le hy.le) 2)
    (Real.rpow_nonneg hy'.le _)

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
  for name in [``ManuscriptAudit.ThetaInfinityCusp.weighted_jacobiTheta_memLp_infinity,
      ``ManuscriptAudit.ThetaInfinityCusp.jacobiTheta_half_memLp_infinity] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
