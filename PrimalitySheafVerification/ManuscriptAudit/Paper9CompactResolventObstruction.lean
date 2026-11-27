import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CompactInverseSeparatedApproximateEigenvectors
import PrimalitySheafVerification.ManuscriptAudit.Paper9OrthogonalCuspWaves
import PrimalitySheafVerification.ManuscriptAudit.Paper9SmoothWaveLeftInverse

/-! Actual unit cusp waves rule out a compact inverse for a matching realization. -/

namespace ManuscriptAudit.Paper9CompactResolventObstruction

open Filter MeasureTheory
open Paper9CuspWaveHilbert Paper9OrthogonalCuspWaves Paper9QuotientCuspWave
open Paper9LogCuspWave Paper9LogCuspWaveMass HyperbolicCuspGaugeTest
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry
open scoped Topology

noncomputable section

theorem scale_one_le (n : ℕ) : 1 ≤ scale n := by
  unfold scale
  exact one_le_pow₀ (by norm_num)

theorem scale_tendsto : Tendsto scale atTop atTop := by
  unfold scale
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

theorem no_compact_resolvent_inverse (D : GammaTwoFundamentalDomain)
    (T : quotientL2 D →ₗ.[ℂ] quotientL2 D) (k : ℝ) (μ : ℂ)
    (hDomain : ∀ R (hR : 1 ≤ R), waveVector D k R (zero_lt_one.trans_le hR) ∈ T.domain)
    (hResidual : ∀ R (hR : 1 ≤ R),
      ‖T ⟨waveVector D k R (zero_lt_one.trans_le hR), hDomain R hR⟩ -
        (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) • waveVector D k R (zero_lt_one.trans_le hR)‖ ^ (2 : ℕ) =
      ∫ q, squaredDensity (residual (deriv cuspBump) (deriv (deriv cuspBump)) k R)
        (Real.exp R) (Real.exp (R * 6)) q ∂D.quotientMeasure) :
    ¬ ∃ B : quotientL2 D →L[ℂ] quotientL2 D,
      IsCompactOperator (B : quotientL2 D →ₗ[ℂ] quotientL2 D) ∧
      ∀ v : T.domain, B (T v - μ • (v : quotientL2 D)) = v := by
  let eigenvalue : ℂ := -((1 / 4 + k ^ 2 : ℝ) : ℂ)
  let v (n : ℕ) : T.domain :=
    ⟨waveVector D k (scale n) (scale_positive n), hDomain (scale n) (scale_one_le n)⟩
  let c (n : ℕ) : ℂ := ((‖(v n : quotientL2 D)‖ : ℂ)⁻¹)
  let u (n : ℕ) : T.domain := c n • v n
  let e (n : ℕ) := T (u n) - eigenvalue • (u n : quotientL2 D)
  have hu (n : ℕ) : (u n : quotientL2 D) = normalizedWave D k n := rfl
  have h1 : ContDiff ℝ 1 cuspBump := contDiff_infty.mp cuspBump_smooth 1
  have h2 : ContDiff ℝ (1 + 1) cuspBump := contDiff_infty.mp cuspBump_smooth 2
  have hd : ContDiff ℝ 1 (deriv cuspBump) := (contDiff_succ_iff_deriv.mp h2).2.2
  have hM : 0 < mass cuspBump 1 6 := by
    have h : 0 < 2 * mass cuspBump 1 6 := cuspMass_pos
    linarith only [h]
  have hSq (n : ℕ) : ‖e n‖ ^ 2 =
      relativeResidual cuspBump (deriv cuspBump) (deriv (deriv cuspBump)) 1 6 k (scale n) := by
    have hResidualForm : e n = c n • (T (v n) - eigenvalue • (v n : quotientL2 D)) := by
      change T (c n • v n) - eigenvalue • (c n • (v n : quotientL2 D)) = _
      rw [map_smul, smul_sub, smul_comm eigenvalue]
    rw [hResidualForm, norm_smul, c, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), mul_pow, inv_pow, mul_comm, ← div_eq_mul_inv]
    have hA : ‖T (v n) - eigenvalue • (v n : quotientL2 D)‖ ^ (2 : ℕ) = _ :=
      hResidual (scale n) (scale_one_le n)
    have hB : ‖(v n : quotientL2 D)‖ ^ (2 : ℕ) = _ :=
      waveVector_norm_sq D k (scale n) (scale_positive n)
    rw [hA, hB]
    exact quotient_relative_eq D cuspBump (deriv cuspBump) (deriv (deriv cuspBump)) k (scale n)
      (scale_positive n) (fun t => ((h1.differentiable (by decide)) t).hasDerivAt)
      h1.continuous_deriv_one hd.continuous_deriv_one hM.ne'
  have hSqLim : Tendsto (fun n => ‖e n‖ ^ 2) atTop (𝓝 0) := by
    have hLim := (relative_tendsto_zero cuspBump (deriv cuspBump)
      (deriv (deriv cuspBump)) 1 6 k).comp scale_tendsto
    have hEq :
        (relativeResidual cuspBump (deriv cuspBump) (deriv (deriv cuspBump)) 1 6 k ∘ scale) =
          (fun n => ‖e n‖ ^ 2) := funext (fun n => (hSq n).symm)
    rw [hEq] at hLim
    exact hLim
  have hNormLim : Tendsto (fun n => ‖e n‖) atTop (𝓝 0) := by
    have h : Tendsto (Real.sqrt ∘ fun n => ‖e n‖ ^ 2) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.continuousAt : ContinuousAt Real.sqrt 0).tendsto.comp hSqLim
    have hEq : (Real.sqrt ∘ fun n => ‖e n‖ ^ 2) = (fun n => ‖e n‖) :=
      funext (fun n => Real.sqrt_sq (norm_nonneg (e n)))
    rw [hEq, Real.sqrt_zero] at h
    exact h
  exact CompactInverseSeparatedApproximateEigenvectors.no_compact_left_inverse T u eigenvalue μ
    (fun n => by rw [hu, normalizedWave_norm])
    (fun m n h => by rw [hu m, hu n]; exact normalizedWave_separation D k h)
    (tendsto_zero_iff_norm_tendsto_zero.mpr hNormLim)

end
end ManuscriptAudit.Paper9CompactResolventObstruction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9CompactResolventObstruction.no_compact_resolvent_inverse
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
