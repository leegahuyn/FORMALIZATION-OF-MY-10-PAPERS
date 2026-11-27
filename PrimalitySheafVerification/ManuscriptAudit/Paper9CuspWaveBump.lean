import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HyperbolicCuspGaugeTest
import PrimalitySheafVerification.ManuscriptAudit.Paper9QuotientCuspWave

/-! A fixed nonzero smooth cutoff realizes the small-residual modes. -/

namespace ManuscriptAudit.Paper9CuspWaveBump

open Filter MeasureTheory Set HyperbolicCuspGaugeTest
open Paper9LogCuspWave Paper9LogCuspWaveMass Paper9QuotientCuspWave
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped Topology ContDiff

noncomputable section

private theorem derivatives_zero {t : ℝ} (ht : t < 2 ∨ 5 < t) :
    cuspBump t = 0 ∧ deriv cuspBump t = 0 ∧ deriv (deriv cuspBump) t = 0 := by
  have he : cuspBump =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    rcases ht with h | h
    · filter_upwards [Iio_mem_nhds h] with x hx
      exact cuspBump_zero_of_height_outside (Or.inl hx.le)
    · filter_upwards [Ioi_mem_nhds h] with x hx
      exact cuspBump_zero_of_height_outside (Or.inr hx.le)
  have hd : deriv cuspBump =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    simpa only [deriv_const] using he.deriv
  exact ⟨he.eq_of_nhds, hd.eq_of_nhds, by simpa only [deriv_const] using hd.deriv_eq⟩

theorem zero_outside_log_slab (k R t : ℝ) (hR : 0 < R) (ht : t ≤ R ∨ R * 6 ≤ t) :
    trial cuspBump k R t = 0 ∧
      residual (deriv cuspBump) (deriv (deriv cuspBump)) k R t = 0 := by
  have hPos : t / R < 2 ∨ 5 < t / R := by
    rcases ht with h | h
    · exact Or.inl ((div_lt_iff₀ hR).mpr (by linarith))
    · exact Or.inr ((lt_div_iff₀ hR).mpr (by linarith))
  obtain ⟨h0, h1, h2⟩ := derivatives_zero hPos
  simp [trial, residual, amplitude, h0, h1, h2]

theorem exists_small_residual_of_cuspBump (D : GammaTwoFundamentalDomain) (k : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      (∫ q, squaredDensity (residual (deriv cuspBump) (deriv (deriv cuspBump)) k R)
          (Real.exp R) (Real.exp (R * 6)) q ∂D.quotientMeasure) <
        ε * (∫ q, squaredDensity (trial cuspBump k R) (Real.exp R) (Real.exp (R * 6)) q
          ∂D.quotientMeasure) := by
  have h1 : ContDiff ℝ 1 cuspBump := contDiff_infty.mp cuspBump_smooth 1
  have h2 : ContDiff ℝ (1 + 1) cuspBump := contDiff_infty.mp cuspBump_smooth 2
  have hd : ContDiff ℝ 1 (deriv cuspBump) := (contDiff_succ_iff_deriv.mp h2).2.2
  have hM : 0 < mass cuspBump 1 6 := by
    have h : 0 < 2 * mass cuspBump 1 6 := cuspMass_pos
    linarith only [h]
  exact exists_small_quotient_residual D cuspBump (deriv cuspBump) (deriv (deriv cuspBump)) k
    (fun t => ((h1.differentiable (by decide)) t).hasDerivAt)
    h1.continuous_deriv_one hd.continuous_deriv_one hM hε

end
end ManuscriptAudit.Paper9CuspWaveBump

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspWaveBump.zero_outside_log_slab,
      ``ManuscriptAudit.Paper9CuspWaveBump.exists_small_residual_of_cuspBump] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
