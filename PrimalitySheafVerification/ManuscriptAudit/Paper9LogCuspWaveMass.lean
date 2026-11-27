import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper9LogCuspWave

/-! Dilated waves have arbitrarily small relative residual on log-height slabs. -/

namespace ManuscriptAudit.Paper9LogCuspWaveMass

open Filter MeasureTheory Set Paper9LogCuspWave
open scoped Topology

noncomputable section

def mass (b : ℝ → ℝ) (a d : ℝ) : ℝ := ∫ t in a..d, b t ^ (2 : ℕ)

def relativeResidual (b b' b'' : ℝ → ℝ) (a d k R : ℝ) : ℝ :=
  ((R⁻¹) ^ 4 * mass b'' a d + (4 * k ^ 2 * mass b' a d) * (R⁻¹) ^ 2) / mass b a d

private theorem scale_integral (f : ℝ → ℝ) (a d R : ℝ) (hR : R ≠ 0) :
    (∫ t in (R * a)..(R * d), f (t / R)) = R * ∫ t in a..d, f t := by
  rw [intervalIntegral.integral_comp_div f hR, smul_eq_mul]
  rw [show R * a / R = a by field_simp [hR] <;> ring,
    show R * d / R = d by field_simp [hR] <;> ring]

theorem trial_mass (b : ℝ → ℝ) (a d k R : ℝ) (hR : R ≠ 0) :
    (∫ t in (R * a)..(R * d), ‖trial b k R t‖ ^ (2 : ℕ)) = R * mass b a d := by
  simp_rw [trial_norm_sq]
  exact scale_integral (fun v => b v ^ (2 : ℕ)) a d R hR

theorem residual_mass (b' b'' : ℝ → ℝ) (a d k R : ℝ) (hR : R ≠ 0)
    (hb' : Continuous b') (hb'' : Continuous b'') :
    (∫ t in (R * a)..(R * d), ‖residual b' b'' k R t‖ ^ (2 : ℕ)) =
      R * ((R⁻¹) ^ 4 * mass b'' a d + (4 * k ^ 2 * mass b' a d) * (R⁻¹) ^ 2) := by
  have hEq (t : ℝ) : ‖residual b' b'' k R t‖ ^ (2 : ℕ) =
      (R⁻¹) ^ 4 * b'' (t / R) ^ (2 : ℕ) +
        (4 * k ^ 2 * (R⁻¹) ^ 2) * b' (t / R) ^ (2 : ℕ) := by
    rw [residual_norm_sq]
    ring
  simp_rw [hEq]
  have hScale : Continuous (fun t : ℝ => t / R) := continuous_id.div_const R
  have hA : IntervalIntegrable (fun t : ℝ => (R⁻¹) ^ 4 * b'' (t / R) ^ (2 : ℕ))
      volume (R * a) (R * d) :=
    (continuous_const.mul ((hb''.comp hScale).pow 2)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t : ℝ => (4 * k ^ 2 * (R⁻¹) ^ 2) * b' (t / R) ^ (2 : ℕ))
      volume (R * a) (R * d) :=
    (continuous_const.mul ((hb'.comp hScale).pow 2)).intervalIntegrable _ _
  calc
    _ = (∫ t in (R * a)..(R * d), (R⁻¹) ^ 4 * b'' (t / R) ^ (2 : ℕ)) +
        (∫ t in (R * a)..(R * d), (4 * k ^ 2 * (R⁻¹) ^ 2) * b' (t / R) ^ (2 : ℕ)) :=
      intervalIntegral.integral_add hA hB
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        scale_integral (fun t => b'' t ^ (2 : ℕ)) a d R hR,
        scale_integral (fun t => b' t ^ (2 : ℕ)) a d R hR]
      unfold mass
      ring

theorem relative_eq (b b' b'' : ℝ → ℝ) (a d k R : ℝ) (hR : R ≠ 0)
    (hb' : Continuous b') (hb'' : Continuous b'') (hM : mass b a d ≠ 0) :
    (∫ t in (R * a)..(R * d), ‖residual b' b'' k R t‖ ^ (2 : ℕ)) /
        (∫ t in (R * a)..(R * d), ‖trial b k R t‖ ^ (2 : ℕ)) =
      relativeResidual b b' b'' a d k R := by
  rw [residual_mass b' b'' a d k R hR hb' hb'', trial_mass b a d k R hR]
  unfold relativeResidual
  field_simp [hR, hM]

theorem relative_tendsto_zero (b b' b'' : ℝ → ℝ) (a d k : ℝ) :
    Tendsto (relativeResidual b b' b'' a d k) atTop (𝓝 0) := by
  have hI : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hA := (hI.pow 4).mul (tendsto_const_nhds (x := mass b'' a d))
  have hB := (tendsto_const_nhds (x := 4 * k ^ 2 * mass b' a d)).mul (hI.pow 2)
  unfold relativeResidual
  simpa only [zero_pow (by decide : (4 : ℕ) ≠ 0), zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_mul, mul_zero, zero_add, zero_div] using (hA.add hB).div_const (mass b a d)

theorem exists_small_relative_residual (b b' b'' : ℝ → ℝ) (a d k : ℝ)
    (hb' : Continuous b') (hb'' : Continuous b'') (hM : 0 < mass b a d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      (∫ t in (R * a)..(R * d), ‖residual b' b'' k R t‖ ^ (2 : ℕ)) <
        ε * (∫ t in (R * a)..(R * d), ‖trial b k R t‖ ^ (2 : ℕ)) := by
  have he : ∀ᶠ R : ℝ in atTop, relativeResidual b b' b'' a d k R < ε :=
    (relative_tendsto_zero b b' b'' a d k).eventually (Iio_mem_nhds hε)
  obtain ⟨R, hR, hLt⟩ := ((eventually_ge_atTop (1 : ℝ)).and he).exists
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hMass : 0 < ∫ t in (R * a)..(R * d), ‖trial b k R t‖ ^ (2 : ℕ) := by
    rw [trial_mass b a d k R hR0.ne']
    positivity
  refine ⟨R, hR, (div_lt_iff₀ hMass).mp ?_⟩
  rw [relative_eq b b' b'' a d k R hR0.ne' hb' hb'' hM.ne']
  exact hLt

end
end ManuscriptAudit.Paper9LogCuspWaveMass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9LogCuspWaveMass.trial_mass,
      ``ManuscriptAudit.Paper9LogCuspWaveMass.residual_mass,
      ``ManuscriptAudit.Paper9LogCuspWaveMass.relative_eq,
      ``ManuscriptAudit.Paper9LogCuspWaveMass.relative_tendsto_zero,
      ``ManuscriptAudit.Paper9LogCuspWaveMass.exists_small_relative_residual] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
