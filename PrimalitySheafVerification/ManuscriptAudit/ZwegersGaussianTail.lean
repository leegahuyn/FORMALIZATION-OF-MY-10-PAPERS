import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Gaussian tail in the Zwegers correction

The normalized error integral has odd parity. Away from the origin,
its difference from the real sign function is bounded by the Gaussian
tail obtained by integrating the weighted Gaussian exactly.
-/

namespace ManuscriptAudit.ZwegersGaussianTail

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

private def gaussian (t : ℝ) : ℝ := Real.exp (-Real.pi * t ^ 2)

/-- Zwegers' normalized real error integral. -/
def errorIntegral (x : ℝ) : ℝ :=
  2 * (∫ t in (0 : ℝ)..x, gaussian t)

private theorem gaussian_neg (t : ℝ) : gaussian (-t) = gaussian t := by
  simp [gaussian, neg_sq]

/-- The normalized error integral is odd. -/
theorem errorIntegral_neg (x : ℝ) : errorIntegral (-x) = -errorIntegral x := by
  have h : (∫ t in (0 : ℝ)..x, gaussian t) = ∫ t in -x..(0 : ℝ), gaussian t := by
    simpa only [gaussian_neg, neg_zero] using
      (intervalIntegral.integral_comp_neg (f := gaussian) (a := (0 : ℝ)) (b := x))
  have hs : (∫ t in (0 : ℝ)..(-x), gaussian t) = -(∫ t in -x..(0 : ℝ), gaussian t) :=
    intervalIntegral.integral_symm (-x) 0
  unfold errorIntegral
  rw [hs, ← h, mul_neg]

private theorem gaussian_integrable : Integrable gaussian :=
  integrable_exp_neg_mul_sq Real.pi_pos

private theorem weighted_gaussian_integrable : Integrable (fun t : ℝ => t * gaussian t) :=
  integrable_mul_exp_neg_mul_sq Real.pi_pos

private theorem gaussian_half_integral : (∫ t in Ioi (0 : ℝ), gaussian t) = 1 / 2 := by
  unfold gaussian
  rw [integral_gaussian_Ioi, div_self Real.pi_pos.ne', Real.sqrt_one]

private theorem one_sub_errorIntegral_eq_tail {x : ℝ} (hx : 0 < x) :
    1 - errorIntegral x = 2 * (∫ t in Ioi x, gaussian t) := by
  have hd : Disjoint (Ioc (0 : ℝ) x) (Ioi x) :=
    Set.disjoint_left.mpr fun _ ht htx => (not_lt_of_ge ht.2) htx
  have hSum := setIntegral_union hd measurableSet_Ioi
    (gaussian_integrable.integrableOn (s := Ioc (0 : ℝ) x))
    (gaussian_integrable.integrableOn (s := Ioi x))
  rw [Ioc_union_Ioi_eq_Ioi hx.le, gaussian_half_integral] at hSum
  unfold errorIntegral
  rw [intervalIntegral.integral_of_le hx.le]
  linarith

private def gaussianPrimitive (t : ℝ) : ℝ :=
  -(2 * Real.pi)⁻¹ * gaussian t

private theorem gaussianPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianPrimitive (t * gaussian t) t := by
  unfold gaussianPrimitive gaussian
  convert! (((hasDerivAt_pow 2 t).const_mul (-Real.pi)).exp.const_mul
    (-(2 * Real.pi)⁻¹)) using 1 <;> field_simp [Real.pi_pos.ne'] <;> ring

private theorem gaussianPrimitive_tendsto : Tendsto gaussianPrimitive atTop (𝓝 0) := by
  have h : Tendsto gaussian atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.2 Real.pi_pos))
  simpa [gaussianPrimitive] using Tendsto.const_mul (-(2 * Real.pi)⁻¹) h

private theorem integral_weighted_gaussian_tail (x : ℝ) :
    (∫ t in Ioi x, t * gaussian t) = gaussian x / (2 * Real.pi) := by
  calc
    _ = 0 - gaussianPrimitive x :=
      integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => gaussianPrimitive_hasDerivAt t)
        weighted_gaussian_integrable.integrableOn gaussianPrimitive_tendsto
    _ = _ := by simp [gaussianPrimitive, div_eq_mul_inv, mul_comm]

private theorem tail_bound_of_pos {x : ℝ} (hx : 0 < x) :
    |Real.sign x - errorIntegral x| ≤ gaussian x / (Real.pi * |x|) := by
  rw [Real.sign_of_pos hx, one_sub_errorIntegral_eq_tail hx, abs_of_pos hx]
  have hNonneg : 0 ≤ ∫ t in Ioi x, gaussian t :=
    setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le)
  rw [abs_of_nonneg (mul_nonneg (by norm_num) hNonneg)]
  have hM : (∫ t in Ioi x, gaussian t) ≤ ∫ t in Ioi x, x⁻¹ * (t * gaussian t) := by
    apply setIntegral_mono_on gaussian_integrable.integrableOn
      (weighted_gaussian_integrable.const_mul x⁻¹).integrableOn measurableSet_Ioi
    intro t ht
    calc
      gaussian t = x⁻¹ * (x * gaussian t) := by
        rw [← mul_assoc, inv_mul_cancel₀ hx.ne', one_mul]
      _ ≤ x⁻¹ * (t * gaussian t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_of_lt ht) (Real.exp_pos _).le)
          (inv_nonneg.mpr hx.le)
  rw [integral_const_mul, integral_weighted_gaussian_tail] at hM
  calc
    _ ≤ 2 * (x⁻¹ * (gaussian x / (2 * Real.pi))) :=
      mul_le_mul_of_nonneg_left hM (by norm_num)
    _ = _ := by
      field_simp [hx.ne', Real.pi_pos.ne'] <;> ring

/-- For every nonzero input, the sign defect is bounded by the Gaussian tail. -/
theorem sign_sub_errorIntegral_abs_le (x : ℝ) (hx : x ≠ 0) :
    |Real.sign x - errorIntegral x| ≤ Real.exp (-Real.pi * x ^ 2) / (Real.pi * |x|) := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · have he : Real.sign (-x) - errorIntegral (-x) = -(Real.sign x - errorIntegral x) := by
      rw [Real.sign_neg, errorIntegral_neg]
      ring
    simpa only [he, abs_neg, gaussian_neg, gaussian, neg_sq] using tail_bound_of_pos (neg_pos.mpr hn)
  · exact tail_bound_of_pos hp

end

end ManuscriptAudit.ZwegersGaussianTail

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ZwegersGaussianTail.errorIntegral_neg,
      ``ManuscriptAudit.ZwegersGaussianTail.sign_sub_errorIntegral_abs_le] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
