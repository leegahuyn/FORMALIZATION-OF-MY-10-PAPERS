import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspWaveHilbert

/-! Waves in disjoint cusp slabs are orthogonal in the native quotient Hilbert space. -/

namespace ManuscriptAudit.Paper9OrthogonalCuspWaves

open Filter MeasureTheory
open scoped Topology
open ThetaChosenQuotientAnalysis GammaTwoQuotientHeightIntegral
open Paper9CuspWaveHilbert Paper9CuspWaveQuotientCoefficient Paper9SmoothCuspWave
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry

noncomputable section

theorem orthogonal_of_separation (D : GammaTwoFundamentalDomain) (k R S : ℝ)
    (hR : 0 < R) (hS : 0 < S) (hSep : R * 6 ≤ S) :
    inner ℂ (waveVector D k R hR) (waveVector D k S hS) = 0 := by
  let f := waveVector D k R hR
  let g := waveVector D k S hS
  have hf : (f : GammaTwoQuotient → ℂ) =ᵐ[D.quotientMeasure] unitThetaCoefficient k R :=
    (unitThetaCoefficient_memLp D k R hR).coeFn_toLp
  have hg : (g : GammaTwoQuotient → ℂ) =ᵐ[D.quotientMeasure] unitThetaCoefficient k S :=
    (unitThetaCoefficient_memLp D k S hS).coeFn_toLp
  change inner ℂ f g = 0
  rw [MeasureTheory.L2.inner_def]
  have hZero : (fun q => inner ℂ (f q) (g q)) =ᵐ[D.quotientMeasure] fun _ => 0 := by
    filter_upwards [hf, hg] with q hqf hqg
    by_cases h : quotientHeight q ≤ Real.exp S
    · have hz : unitThetaCoefficient k S q = 0 := norm_eq_zero.mp (by
        rw [unitThetaCoefficient_norm k S hS q, chartAmplitude_zero_below k S _ hS h, norm_zero])
      rw [hqg, hz, inner_zero_right]
    · have hAbove : Real.exp (R * 6) ≤ quotientHeight q :=
        (Real.exp_le_exp.mpr hSep).trans (lt_of_not_ge h).le
      have hz : unitThetaCoefficient k R q = 0 := norm_eq_zero.mp (by
        rw [unitThetaCoefficient_norm k R hR q, chartAmplitude_zero_above k R _ hR hAbove, norm_zero])
      rw [hqf, hz, inner_zero_left]
  simpa only [integral_zero] using integral_congr_ae hZero

/-- The widths increase and all slabs are disjoint. -/
def scale (n : ℕ) : ℝ := 7 ^ n

theorem scale_positive (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

theorem scale_separated {m n : ℕ} (h : m < n) : scale m * 6 ≤ scale n := by
  calc
    _ ≤ scale m * 7 := mul_le_mul_of_nonneg_left (by norm_num) (scale_positive m).le
    _ = scale (m + 1) := by simp only [scale, pow_succ]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 7) (Nat.succ_le_of_lt h)

/-- A countable family of actual nonzero orthogonal waves at any fixed frequency. -/
theorem sequence_orthogonal (D : GammaTwoFundamentalDomain) (k : ℝ) {m n : ℕ} (hmn : m < n) :
    inner ℂ (waveVector D k (scale m) (scale_positive m))
      (waveVector D k (scale n) (scale_positive n)) = 0 :=
  orthogonal_of_separation D k _ _ _ _ (scale_separated hmn)

def normalizedWave (D : GammaTwoFundamentalDomain) (k : ℝ) (n : ℕ) : quotientL2 D :=
  let v := waveVector D k (scale n) (scale_positive n)
  ((‖v‖ : ℂ)⁻¹) • v

theorem normalizedWave_norm (D : GammaTwoFundamentalDomain) (k : ℝ) (n : ℕ) :
    ‖normalizedWave D k n‖ = 1 := by
  let v := waveVector D k (scale n) (scale_positive n)
  have h := waveVector_norm_pos D k (scale n) (scale_positive n)
  change ‖((‖v‖ : ℂ)⁻¹) • v‖ = 1
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ h.ne'

theorem normalizedWave_orthogonal (D : GammaTwoFundamentalDomain) (k : ℝ) {m n : ℕ} (h : m < n) :
    inner ℂ (normalizedWave D k m) (normalizedWave D k n) = 0 := by
  simp only [normalizedWave, inner_smul_left, inner_smul_right, sequence_orthogonal D k h,
    mul_zero, zero_mul]

theorem normalizedWave_separation (D : GammaTwoFundamentalDomain) (k : ℝ) {m n : ℕ} (h : m < n) :
    1 ≤ dist (normalizedWave D k m) (normalizedWave D k n) := by
  have hSq : dist (normalizedWave D k m) (normalizedWave D k n) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ), normalizedWave_norm D k m, normalizedWave_norm D k n,
      normalizedWave_orthogonal D k h] <;> norm_num
  by_contra hn
  have hlt : dist (normalizedWave D k m) (normalizedWave D k n) < 1 := lt_of_not_ge hn
  let d := dist (normalizedWave D k m) (normalizedWave D k n)
  have hd : 0 ≤ d := dist_nonneg
  have hProd : 0 < (1 - d) * (1 + d) :=
    mul_pos (sub_pos.mpr hlt) (by linarith)
  change d ^ 2 = 2 at hSq
  nlinarith

theorem normalizedWave_orthonormal (D : GammaTwoFundamentalDomain) (k : ℝ) :
    Orthonormal ℂ (normalizedWave D k) := by
  refine ⟨normalizedWave_norm D k, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact normalizedWave_orthogonal D k h
  · rw [← inner_conj_symm, normalizedWave_orthogonal D k h, map_zero]

theorem normalizedWave_inner_tendsto_zero (D : GammaTwoFundamentalDomain) (k : ℝ)
    (x : quotientL2 D) :
    Tendsto (fun n => inner ℂ (normalizedWave D k n) x) atTop (𝓝 0) := by
  have hSum := (normalizedWave_orthonormal D k).inner_products_summable x
  have hSq := hSum.tendsto_atTop_zero
  let y (n : ℕ) := ‖inner ℂ (normalizedWave D k n) x‖
  have h : Tendsto (Real.sqrt ∘ fun n => y n ^ 2) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.continuousAt : ContinuousAt Real.sqrt 0).tendsto.comp hSq
  have he : (Real.sqrt ∘ fun n => y n ^ 2) = y :=
    funext (fun n => Real.sqrt_sq (norm_nonneg (inner ℂ (normalizedWave D k n) x)))
  rw [he, Real.sqrt_zero] at h
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h

end
end ManuscriptAudit.Paper9OrthogonalCuspWaves

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9OrthogonalCuspWaves.orthogonal_of_separation,
      ``ManuscriptAudit.Paper9OrthogonalCuspWaves.scale_separated,
      ``ManuscriptAudit.Paper9OrthogonalCuspWaves.sequence_orthogonal,
      ``ManuscriptAudit.Paper9OrthogonalCuspWaves.normalizedWave_norm,
      ``ManuscriptAudit.Paper9OrthogonalCuspWaves.normalizedWave_orthogonal,
      ``ManuscriptAudit.Paper9OrthogonalCuspWaves.normalizedWave_separation,
      ``ManuscriptAudit.Paper9OrthogonalCuspWaves.normalizedWave_orthonormal,
      ``ManuscriptAudit.Paper9OrthogonalCuspWaves.normalizedWave_inner_tendsto_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
