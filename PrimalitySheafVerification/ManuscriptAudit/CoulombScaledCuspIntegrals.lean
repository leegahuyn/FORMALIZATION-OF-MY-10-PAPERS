import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombScaledCuspForms

/-! Exact mass and covariant energy under affine rescaling in the width-two cusp. -/

namespace ManuscriptAudit.CoulombScaledCuspIntegrals

open Filter MeasureTheory Set HyperbolicCuspGaugeTest CoulombScaledCuspForms
open scoped ContDiff Topology

noncomputable section

def mass (r : ℝ) : ℝ := 2 * ∫ y : ℝ in (1 : ℝ)..6, amplitude r y ^ 2

def energy (r : ℝ) : ℝ :=
  2 * ∫ y : ℝ in (1 : ℝ)..6, amplitude r y ^ 2 + (y * deriv (amplitude r) y + amplitude r y) ^ 2

def pulledEnergy (r t : ℝ) : ℝ :=
  cuspBump t ^ 2 + ((t - shift r) * deriv cuspBump t + cuspBump t) ^ 2

theorem bump_deriv_continuous : Continuous (deriv cuspBump) :=
  (contDiff_infty.mp cuspBump_smooth 1).continuous_deriv_one

private theorem bump_deriv_zero (t : ℝ) (ht : t < 2 ∨ 5 < t) : deriv cuspBump t = 0 := by
  have he : cuspBump =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    rcases ht with ht | ht
    · filter_upwards [Iio_mem_nhds ht] with y hy
      exact cuspBump_zero_of_height_outside (Or.inl (le_of_lt hy))
    · filter_upwards [Ioi_mem_nhds ht] with y hy
      exact cuspBump_zero_of_height_outside (Or.inr (le_of_lt hy))
  simpa only [deriv_const] using he.deriv_eq

private theorem interval_eq_fixed (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ}
    (ha : a ≤ 1) (hb : 6 ≤ b)
    (hzero : ∀ t, t ≤ 1 ∨ 6 ≤ t → f t = 0) :
    (∫ t in a..b, f t) = ∫ t in (1 : ℝ)..6, f t := by
  have h0 : (∫ t in a..1, f t) = 0 := by
    calc
      _ = ∫ _ : ℝ in a..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le ha]
        intro t ht
        exact hzero t (Or.inl ht.2)
      _ = _ := by simp
  have h1 : (∫ t in (6 : ℝ)..b, f t) = 0 := by
    calc
      _ = ∫ _ : ℝ in (6 : ℝ)..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hb]
        intro t ht
        exact hzero t (Or.inr ht.1)
      _ = _ := by simp
  have hL := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable a 1) (hf.intervalIntegrable 1 6)
  have hR := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable a 6) (hf.intervalIntegrable 6 b)
  rw [h0, zero_add] at hL
  rw [h1, add_zero, ← hL] at hR
  exact hR.symm

private theorem scaled_integral (r : ℝ) (hr : 1 ≤ r) (f : ℝ → ℝ) (hf : Continuous f)
    (hzero : ∀ t, t ≤ 1 ∨ 6 ≤ t → f t = 0) :
    (∫ y : ℝ in (1 : ℝ)..6, f (scaleHeight r y)) =
      r⁻¹ * ∫ t : ℝ in (1 : ℝ)..6, f t := by
  have hr0 : r ≠ 0 := by linarith
  simp only [scaleHeight]
  rw [intervalIntegral.integral_comp_mul_add f hr0 (shift r), smul_eq_mul]
  rw [interval_eq_fixed f hf (by unfold shift; linarith) (by unfold shift; linarith) hzero]

theorem mass_rescaled (r : ℝ) (hr : 1 ≤ r) :
    mass r = (2 * r⁻¹) * (∫ t : ℝ in (1 : ℝ)..6, cuspBump t ^ 2) := by
  have hz (t : ℝ) (ht : t ≤ 1 ∨ 6 ≤ t) : cuspBump t ^ 2 = 0 := by
    rw [cuspBump_zero_of_height_outside (ht.imp (by intro h; linarith) (by intro h; linarith))]
    norm_num
  unfold mass amplitude
  rw [scaled_integral r hr (fun t => cuspBump t ^ 2) (cuspBump_smooth.continuous.pow 2) hz]
  ring

theorem energy_rescaled (r : ℝ) (hr : 1 ≤ r) :
    energy r = (2 * r⁻¹) * (∫ t : ℝ in (1 : ℝ)..6, pulledEnergy r t) := by
  have hb := cuspBump_smooth.continuous
  have hc : Continuous (pulledEnergy r) :=
    (hb.pow 2).add ((((continuous_id.sub continuous_const).mul bump_deriv_continuous).add hb).pow 2)
  have hz (t : ℝ) (ht : t ≤ 1 ∨ 6 ≤ t) : pulledEnergy r t = 0 := by
    rw [pulledEnergy,
      cuspBump_zero_of_height_outside (ht.imp (by intro h; linarith) (by intro h; linarith)),
      bump_deriv_zero t (ht.imp (by intro h; linarith) (by intro h; linarith))]
    ring
  have hForm (y : ℝ) : amplitude r y ^ 2 + (y * deriv (amplitude r) y + amplitude r y) ^ 2 =
      pulledEnergy r (scaleHeight r y) := by
    rw [amplitude_deriv, pulledEnergy]
    simp only [amplitude]
    have h : scaleHeight r y - shift r = r * y := by rw [scaleHeight, add_sub_cancel_right]
    rw [h]
    ring
  unfold energy
  simp_rw [hForm]
  rw [scaled_integral r hr (pulledEnergy r) hc hz]
  ring

end
end ManuscriptAudit.CoulombScaledCuspIntegrals

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombScaledCuspIntegrals.mass_rescaled,
      ``ManuscriptAudit.CoulombScaledCuspIntegrals.energy_rescaled] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
