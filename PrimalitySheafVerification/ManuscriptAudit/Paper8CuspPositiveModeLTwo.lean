import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper8CuspPositiveModeGrowth

/-!
# Positive modes vanish under actual weighted cusp square integrability

For an anti-holomorphic bottom-eigenspace profile y^(1/4) * conj H,
the hyperbolic squared norm on the cusp is the horizontal energy of H
divided by y^(3/2). A positive mode forces that energy to be bounded
below by a positive constant on a ray, contradicting integrability.
-/

namespace ManuscriptAudit.Paper8CuspPositiveModeLTwo

open Set MeasureTheory Filter
open Paper8CuspPositiveModeGrowth
open scoped Interval Topology

noncomputable section

def horizontalEnergy (H : ℂ → ℂ) (y : ℝ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..1, ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2

theorem horizontal_mode_energy_bound (H : ℂ → ℂ) (frequency : ℝ)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im})
    {y : ℝ} (hy : 0 < y) :
    ‖conjugatePositiveMode H frequency y‖ ^ 2 ≤ horizontalEnergy H y := by
  let L (x : ℝ) := H ((x : ℂ) + (y : ℂ) * Complex.I)
  let v (x : ℝ) := ‖L x‖
  let a : ℝ := ∫ x : ℝ in (0 : ℝ)..1, v x
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hcL : Continuous L := by
    refine continuous_iff_continuousAt.mpr (fun x => ?_)
    let γ (t : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
    have hIn : γ x ∈ {z : ℂ | 0 < z.im} := by
      simpa [γ, Complex.mul_im] using hy
    have hc : ContinuousAt H (γ x) :=
      hH.continuousOn.continuousAt (hU.mem_nhds hIn)
    have hp : ContinuousAt γ x := by unfold γ; fun_prop
    change ContinuousAt (H ∘ γ) x
    exact hc.comp hp
  have hV : Continuous v := hcL.norm
  have hPhase (x : ℝ) : ‖Complex.exp ((frequency : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hNorm : ‖conjugatePositiveMode H frequency y‖ ≤ a := by
    unfold conjugatePositiveMode a
    calc
      _ ≤ ∫ x : ℝ in (0 : ℝ)..1, ‖L x * Complex.exp ((frequency : ℂ) * Complex.I * (x : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)
      _ = _ := by simp only [norm_mul, hPhase, mul_one, v]
  have hSqInt := (hV.pow 2).intervalIntegrable (0 : ℝ) 1
  have hLinCont : Continuous (fun x : ℝ => (2 * a) * v x) := continuous_const.mul hV
  have hLinInt := hLinCont.intervalIntegrable (0 : ℝ) 1
  have hConstInt : IntervalIntegrable (fun _ : ℝ => a ^ 2) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hExpand : (∫ x : ℝ in (0 : ℝ)..1, (v x - a) ^ 2) = horizontalEnergy H y - a ^ 2 := by
    calc
      _ = ∫ x : ℝ in (0 : ℝ)..1, v x ^ 2 - (2 * a) * v x + a ^ 2 := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hSqInt.sub hLinInt) hConstInt,
          intervalIntegral.integral_sub hSqInt hLinInt, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [sub_zero, one_smul]
        change (∫ x : ℝ in (0 : ℝ)..1, v x ^ 2) - (2 * a) * a + a ^ 2 =
          (∫ x : ℝ in (0 : ℝ)..1, v x ^ 2) - a ^ 2
        ring
  have hPos : 0 ≤ ∫ x : ℝ in (0 : ℝ)..1, (v x - a) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)
  rw [hExpand] at hPos
  exact (pow_le_pow_left₀ (norm_nonneg _) hNorm 2).trans (sub_nonneg.mp hPos)

theorem positive_mode_vanishes (H : ℂ → ℂ) {frequency : ℝ} (hFrequency : 0 < frequency)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) (hT : HasTwistedTranslation H frequency)
    (hLTwo : IntegrableOn (fun y : ℝ => horizontalEnergy H y / y ^ (3 / 2 : ℝ)) (Ioi 1))
    {y₀ : ℝ} (hy₀ : 0 < y₀) : conjugatePositiveMode H frequency y₀ = 0 := by
  by_contra hMode
  let k := (frequency / 2) * ‖conjugatePositiveMode H frequency y₀‖
  have hk : 0 < k := mul_pos (by positivity) (norm_pos_iff.mpr hMode)
  let R := max 2 (2 * y₀)
  have hBound : ∀ y ∈ Ici R, k ^ 2 ≤ horizontalEnergy H y / y ^ (3 / 2 : ℝ) := by
    intro y hy
    have hY : 2 ≤ y := (le_max_left _ _).trans hy
    have hY0 : 0 < y := by linarith
    have hShift : 2 * y₀ ≤ y := (le_max_right _ _).trans hy
    have hExp : (frequency / 2) * y ≤ Real.exp (frequency * (y - y₀)) := by
      have hFirst := mul_le_mul_of_nonneg_left (show y / 2 ≤ y - y₀ by linarith) hFrequency.le
      linarith [Real.add_one_le_exp (frequency * (y - y₀))]
    have hModeBound : k * y ≤ ‖conjugatePositiveMode H frequency y‖ := by
      rw [positive_mode_exponential_growth H frequency hH hT hy₀ hY0, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      unfold k
      calc
        _ = ((frequency / 2) * y) * ‖conjugatePositiveMode H frequency y₀‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hExp (norm_nonneg _)
    have hRpow : y ^ (3 / 2 : ℝ) ≤ y ^ 2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    refine (le_div_iff₀ (Real.rpow_pos_of_pos hY0 _)).2 ?_
    calc
      k ^ 2 * y ^ (3 / 2 : ℝ) ≤ k ^ 2 * y ^ 2 :=
        mul_le_mul_of_nonneg_left hRpow (sq_nonneg _)
      _ = (k * y) ^ 2 := by ring
      _ ≤ ‖conjugatePositiveMode H frequency y‖ ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hk.le hY0.le) hModeBound 2
      _ ≤ horizontalEnergy H y := horizontal_mode_energy_bound H frequency hH hY0
  have hTail : IntegrableOn (fun y : ℝ => horizontalEnergy H y / y ^ (3 / 2 : ℝ)) (Ici R) :=
    hLTwo.mono_set (fun y hy => (by norm_num : (1 : ℝ) < 2).trans_le
      ((le_max_left _ _).trans hy))
  have hConst : Integrable (fun _ : ℝ => k ^ 2) (volume.restrict (Ici R)) := by
    refine hTail.mono' aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    simpa only [Real.norm_of_nonneg (sq_nonneg k)] using hBound y hy
  have hFinite : IsFiniteMeasure (volume.restrict (Ici R)) :=
    (integrable_const_iff_isFiniteMeasure (pow_ne_zero 2 hk.ne')).mp hConst
  have hLess := hFinite.measure_univ_lt_top
  simpa [Measure.restrict_apply MeasurableSet.univ] using hLess

/-- The actual positive-frequency integral, including the (y^{1/4}) weight. -/
theorem weighted_antiHolomorphic_positive_mode_zero (H : ℂ → ℂ) {frequency : ℝ} (hFrequency : 0 < frequency)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) (hT : HasTwistedTranslation H frequency)
    (hLTwo : IntegrableOn (fun y : ℝ => horizontalEnergy H y / y ^ (3 / 2 : ℝ)) (Ioi 1))
    {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ in (0 : ℝ)..1, ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      ((starRingEnd ℂ) (H ((x : ℂ) + (y : ℂ) * Complex.I)) *
        Complex.exp (-((frequency : ℂ) * Complex.I) * (x : ℂ)))) = 0 := by
  have hConj : (∫ x : ℝ in (0 : ℝ)..1,
      (starRingEnd ℂ) (H ((x : ℂ) + (y : ℂ) * Complex.I)) *
        Complex.exp (-((frequency : ℂ) * Complex.I) * (x : ℂ))) =
      (starRingEnd ℂ) (conjugatePositiveMode H frequency y) := by
    unfold conjugatePositiveMode
    rw [← intervalIntegral.intervalIntegral_conj]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    congr 2
    ring
  rw [intervalIntegral.integral_const_mul, hConj,
    positive_mode_vanishes H hFrequency hH hT hLTwo hy, map_zero, mul_zero]

end
end ManuscriptAudit.Paper8CuspPositiveModeLTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8CuspPositiveModeLTwo.horizontal_mode_energy_bound,
      ``ManuscriptAudit.Paper8CuspPositiveModeLTwo.positive_mode_vanishes,
      ``ManuscriptAudit.Paper8CuspPositiveModeLTwo.weighted_antiHolomorphic_positive_mode_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
