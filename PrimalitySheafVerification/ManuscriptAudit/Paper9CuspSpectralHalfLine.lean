import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9ResidualVector

/-!
# The cusp differential has a half-line of approximate eigenvalues

A partial operator on the actual quotient L² that acts as the stated
differential on the smooth compact cusp waves has no bounded left inverse
at the corresponding spectral parameters.
-/

namespace ManuscriptAudit.Paper9CuspSpectralHalfLine

open Paper9CuspWaveHilbert Paper9ResidualVector
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

def parameter (k : ℝ) : ℂ := -((1 / 4 + k^2 : ℝ) : ℂ)

theorem exists_relative_residual (D : GammaTwoFundamentalDomain)
    (T : quotientL2 D →ₗ.[ℂ] quotientL2 D) (k : ℝ)
    (hDomain : ∀ R (hr : 1 ≤ R), waveVector D k R (zero_lt_one.trans_le hr) ∈ T.domain)
    (hAction : ∀ R (hr : 1 ≤ R),
      T ⟨waveVector D k R (zero_lt_one.trans_le hr), hDomain R hr⟩ -
        parameter k • waveVector D k R (zero_lt_one.trans_le hr) =
      residualVector D k R (zero_lt_one.trans_le hr)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : T.domain, 0 < ‖(v : quotientL2 D)‖ ∧
      ‖T v - parameter k • (v : quotientL2 D)‖ < ε * ‖(v : quotientL2 D)‖ := by
  obtain ⟨R, hr, _, _, hNorm, hRes⟩ :=
    exists_smooth_compact_wave_small_residual D k (sq_pos_of_pos hε)
  let w := waveVector D k R (zero_lt_one.trans_le hr)
  let v : T.domain := ⟨w, hDomain R hr⟩
  have hw : 0 < ‖w‖ := waveVector_norm_pos D k R (zero_lt_one.trans_le hr)
  have he : ‖T v - parameter k • w‖^2 < ε^2 * ‖w‖^2 := by
    rw [show T v - parameter k • w = residualVector D k R (zero_lt_one.trans_le hr)
        from hAction R hr, residualVector_norm_sq]
    exact hRes
  refine ⟨v, hw, ?_⟩
  change ‖T v - parameter k • w‖ < ε * ‖w‖
  by_contra! h
  have hpow := pow_le_pow_left₀ (mul_nonneg hε.le hw.le) h 2
  rw [mul_pow] at hpow
  exact he.not_ge hpow

theorem no_bounded_left_inverse (D : GammaTwoFundamentalDomain)
    (T : quotientL2 D →ₗ.[ℂ] quotientL2 D) (k : ℝ)
    (hDomain : ∀ R (hr : 1 ≤ R), waveVector D k R (zero_lt_one.trans_le hr) ∈ T.domain)
    (hAction : ∀ R (hr : 1 ≤ R),
      T ⟨waveVector D k R (zero_lt_one.trans_le hr), hDomain R hr⟩ -
        parameter k • waveVector D k R (zero_lt_one.trans_le hr) =
      residualVector D k R (zero_lt_one.trans_le hr)) :
    ¬ ∃ B : quotientL2 D →L[ℂ] quotientL2 D,
      ∀ v : T.domain, B (T v - parameter k • (v : quotientL2 D)) = v := by
  rintro ⟨B, hB⟩
  let C := ‖B‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨v, hv, he⟩ := exists_relative_residual D T k hDomain hAction (inv_pos.mpr hC)
  let err := T v - parameter k • (v : quotientL2 D)
  have hl : ‖(v : quotientL2 D)‖ ≤ C * ‖err‖ := by
    calc
      _ = ‖B err‖ := congrArg norm (hB v).symm
      _ ≤ ‖B‖ * ‖err‖ := B.le_opNorm err
      _ ≤ C * ‖err‖ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (norm_nonneg err)
  have hlt : C * ‖err‖ < ‖(v : quotientL2 D)‖ := by
    have hh := mul_lt_mul_of_pos_left he hC
    change C * ‖err‖ < C * (C⁻¹ * ‖(v : quotientL2 D)‖) at hh
    rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at hh
    exact hh
  exact hlt.not_ge hl

theorem all_parameters_on_negative_half_line (r : ℝ) (hr : r ≤ -(1 / 4 : ℝ)) :
    ∃ k : ℝ, parameter k = (r : ℂ) := by
  let k := Real.sqrt (-r - 1 / 4)
  have hk : k^2 = -r - 1 / 4 := Real.sq_sqrt (by linarith)
  refine ⟨k, ?_⟩
  have h : -(1 / 4 + k^2) = r := by rw [hk]; ring
  unfold parameter
  exact_mod_cast h

end
end ManuscriptAudit.Paper9CuspSpectralHalfLine

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspSpectralHalfLine.exists_relative_residual,
      ``ManuscriptAudit.Paper9CuspSpectralHalfLine.no_bounded_left_inverse,
      ``ManuscriptAudit.Paper9CuspSpectralHalfLine.all_parameters_on_negative_half_line] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
