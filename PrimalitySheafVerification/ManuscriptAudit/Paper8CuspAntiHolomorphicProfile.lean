import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8CuspPositiveModeLTwo

/-!
# Actual hyperbolic cusp energy in the anti-holomorphic profile

The horizontal integral of the pointwise hyperbolic norm is exactly
the real weighted energy used by the positive-mode vanishing theorem.
-/

namespace ManuscriptAudit.Paper8CuspAntiHolomorphicProfile

open Set MeasureTheory Filter
open Paper8CuspPositiveModeGrowth Paper8CuspPositiveModeLTwo
open scoped Interval

noncomputable section

def weightedProfile (H : ℂ → ℂ) (x y : ℝ) : ℂ :=
  ((y ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
    (starRingEnd ℂ) (H ((x : ℂ) + (y : ℂ) * Complex.I))

def hyperbolicEnergy (H : ℂ → ℂ) (y : ℝ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..1, ‖weightedProfile H x y‖ ^ 2 / y ^ 2

private theorem power_factor {y : ℝ} (hy : 0 < y) :
    (y ^ (1 / 4 : ℝ)) ^ 2 / y ^ 2 = 1 / y ^ (3 / 2 : ℝ) := by
  have hSq : (y ^ (1 / 4 : ℝ)) ^ 2 = y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
  rw [hSq, ← Real.rpow_two y, ← Real.rpow_sub hy]
  rw [show (1 / 2 : ℝ) - 2 = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hy.le, one_div]

theorem hyperbolicEnergy_eq (H : ℂ → ℂ) {y : ℝ} (hy : 0 < y) :
    hyperbolicEnergy H y = horizontalEnergy H y / y ^ (3 / 2 : ℝ) := by
  unfold hyperbolicEnergy
  calc
    _ = ∫ x : ℝ in (0 : ℝ)..1, ((y ^ (1 / 4 : ℝ)) ^ 2 / y ^ 2) *
        ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [weightedProfile, norm_mul, Complex.norm_real, Complex.norm_conj,
        Real.norm_of_nonneg (Real.rpow_nonneg hy.le _), mul_pow]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, power_factor hy, horizontalEnergy]
      ring

theorem actual_profile_positive_mode_zero (H : ℂ → ℂ) {frequency : ℝ} (hf : 0 < frequency)
    (hH : DifferentiableOn ℂ H {z : ℂ | 0 < z.im}) (hT : HasTwistedTranslation H frequency)
    (hLTwo : IntegrableOn (hyperbolicEnergy H) (Ioi 1)) {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ in (0 : ℝ)..1, weightedProfile H x y *
      Complex.exp (-((frequency : ℂ) * Complex.I) * (x : ℂ))) = 0 := by
  have hEnergy : IntegrableOn (fun y : ℝ => horizontalEnergy H y / y ^ (3 / 2 : ℝ)) (Ioi 1) := by
    refine hLTwo.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hyperbolicEnergy_eq H ((by norm_num : (0 : ℝ) < 1).trans hy)
  simpa only [weightedProfile, mul_assoc] using
    weighted_antiHolomorphic_positive_mode_zero H hf hH hT hEnergy hy

end
end ManuscriptAudit.Paper8CuspAntiHolomorphicProfile

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8CuspAntiHolomorphicProfile.hyperbolicEnergy_eq,
      ``ManuscriptAudit.Paper8CuspAntiHolomorphicProfile.actual_profile_positive_mode_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
