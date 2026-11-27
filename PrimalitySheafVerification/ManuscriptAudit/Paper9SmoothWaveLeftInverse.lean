import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspWaveHilbert

/-! The actual compact wave estimates exclude a bounded left inverse at each negative mode. -/

namespace ManuscriptAudit.Paper9SmoothWaveLeftInverse

open MeasureTheory Paper9CuspWaveHilbert Paper9QuotientCuspWave Paper9LogCuspWave
open HyperbolicCuspGaugeTest
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

theorem no_bounded_left_inverse (D : GammaTwoFundamentalDomain)
    (T : quotientL2 D →ₗ.[ℂ] quotientL2 D) (k : ℝ)
    (hDomain : ∀ R (hR : 1 ≤ R), waveVector D k R (zero_lt_one.trans_le hR) ∈ T.domain)
    (hResidual : ∀ R (hR : 1 ≤ R),
      ‖T ⟨waveVector D k R (zero_lt_one.trans_le hR), hDomain R hR⟩ -
        (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) • waveVector D k R (zero_lt_one.trans_le hR)‖ ^ (2 : ℕ) =
      ∫ q, squaredDensity (residual (deriv cuspBump) (deriv (deriv cuspBump)) k R)
        (Real.exp R) (Real.exp (R * 6)) q ∂D.quotientMeasure) :
    ¬ ∃ B : quotientL2 D →L[ℂ] quotientL2 D,
      ∀ v : T.domain, B (T v - (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) • (v : quotientL2 D)) = v := by
  rintro ⟨B, hLeft⟩
  let C : ℝ := ‖B‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₂ : 0 < C ^ (2 : ℕ) := pow_pos hC _
  obtain ⟨R, hR, _, _, _, hSmall⟩ :=
    exists_smooth_compact_wave_small_residual D k (inv_pos.mpr hC₂)
  let v : T.domain := ⟨waveVector D k R (zero_lt_one.trans_le hR), hDomain R hR⟩
  let e : quotientL2 D := T v - (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) • (v : quotientL2 D)
  have hMass : ‖e‖ ^ (2 : ℕ) < (C ^ (2 : ℕ))⁻¹ * ‖(v : quotientL2 D)‖ ^ 2 :=
    (hResidual R hR).trans_lt hSmall
  have hLeft' : B e = (v : quotientL2 D) := hLeft v
  have hNorm : ‖(v : quotientL2 D)‖ ≤ C * ‖e‖ := by
    calc
      _ = ‖B e‖ := congrArg (fun x : quotientL2 D => ‖x‖) hLeft'.symm
      _ ≤ ‖B‖ * ‖e‖ := B.le_opNorm e
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)
  have hLower : ‖(v : quotientL2 D)‖ ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * ‖e‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hDiv : ‖e‖ ^ (2 : ℕ) < ‖(v : quotientL2 D)‖ ^ 2 / C ^ 2 := by
    simpa only [div_eq_mul_inv, mul_comm] using hMass
  have hUpper := (lt_div_iff₀ hC₂).mp hDiv
  exact (not_lt_of_ge hLower) (by simpa only [mul_comm] using hUpper)

end
end ManuscriptAudit.Paper9SmoothWaveLeftInverse

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9SmoothWaveLeftInverse.no_bounded_left_inverse
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
