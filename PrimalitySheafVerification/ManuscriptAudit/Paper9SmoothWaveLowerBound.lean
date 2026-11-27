import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspWaveHilbert

/-! Paper 9, physical p. 410, §1.6.2. The completeness or spectrum of
a realization is unnecessary for the following lower-bound obstruction.
The realization only needs to admit the compact tests and agree with
their measured shifted residual norms. -/

namespace ManuscriptAudit.Paper9SmoothWaveLowerBound

open MeasureTheory Paper9CuspWaveHilbert Paper9QuotientCuspWave Paper9LogCuspWave
open HyperbolicCuspGaugeTest
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped InnerProductSpace

noncomputable section

private theorem re_diagonal_lt_of_small_residual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x y : H) (lambda : ℝ) (hx : 0 < ‖x‖)
    (hSmall : ‖y - (lambda : ℂ) • x‖ ^ (2 : ℕ) < ‖x‖ ^ (2 : ℕ)) :
    (inner ℂ x y).re < (lambda + 1) * ‖x‖ ^ (2 : ℕ) := by
  let e := y - (lambda : ℂ) • x
  have hNorm : ‖e‖ < ‖x‖ := by
    by_contra! h
    have hSq : ‖x‖ ^ (2 : ℕ) ≤ ‖e‖ ^ (2 : ℕ) := by gcongr
    exact (not_lt_of_ge hSq) hSmall
  have hBound : (inner ℂ x e).re < ‖x‖ ^ (2 : ℕ) := by
    calc
      _ ≤ ‖inner ℂ x e‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖e‖ := norm_inner_le_norm _ _
      _ < ‖x‖ * ‖x‖ := mul_lt_mul_of_pos_left hNorm hx
      _ = _ := (pow_two _).symm
  have he : (inner ℂ x e).re = (inner ℂ x y).re - lambda * ‖x‖ ^ (2 : ℕ) := by
    have hxInner : (inner ℂ x x).re = ‖x‖ ^ (2 : ℕ) :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    change (inner ℂ x (y - (lambda : ℂ) • x)).re = _
    rw [inner_sub_right, inner_smul_right]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hxInner]
  rw [he] at hBound
  linarith only [hBound]

private abbrev shiftedResidualMass (D : GammaTwoFundamentalDomain) (k R : ℝ) : ℝ :=
  ∫ q, squaredDensity (residual (deriv cuspBump) (deriv (deriv cuspBump)) k R)
    (Real.exp R) (Real.exp (R * 6)) q ∂D.quotientMeasure

/-- Realizations of the printed sign on these actual smooth compact
tests have real expectations below every proposed quadratic lower bound. -/
theorem test_diagonal_below_every_mass_multiple (D : GammaTwoFundamentalDomain)
    (T : quotientL2 D →ₗ.[ℂ] quotientL2 D)
    (hDomain : ∀ k R (hR : 1 ≤ R), waveVector D k R (zero_lt_one.trans_le hR) ∈ T.domain)
    (hResidual : ∀ k R (hR : 1 ≤ R),
      ‖T ⟨waveVector D k R (zero_lt_one.trans_le hR), hDomain k R hR⟩ -
        (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) • waveVector D k R (zero_lt_one.trans_le hR)‖ ^
        (2 : ℕ) = shiftedResidualMass D k R)
    (b : ℝ) :
    ∃ v : T.domain, 0 < ‖(v : quotientL2 D)‖ ^ (2 : ℕ) ∧
      (inner ℂ (v : quotientL2 D) (T v)).re < b * ‖(v : quotientL2 D)‖ ^ (2 : ℕ) := by
  let k := Real.sqrt (|b| + 2)
  let lambda : ℝ := -(1 / 4 + k ^ 2)
  have hk : k ^ 2 = |b| + 2 := Real.sq_sqrt (by positivity)
  have hb : -|b| ≤ b := by simpa only [neg_neg] using neg_le_neg (neg_le_abs b)
  have hlambda : lambda + 1 < b := by
    change -(1 / 4 + k ^ 2) + 1 < b
    rw [hk]
    linarith only [hb]
  obtain ⟨R, hR, _, _, hMass, hSmall⟩ :=
    exists_smooth_compact_wave_small_residual D k (by norm_num : (0 : ℝ) < 1)
  let v : T.domain := ⟨waveVector D k R (zero_lt_one.trans_le hR), hDomain k R hR⟩
  have hNormSq : 0 < ‖(v : quotientL2 D)‖ ^ (2 : ℕ) := hMass
  have hNorm : 0 < ‖(v : quotientL2 D)‖ := by
    have h := norm_nonneg (v : quotientL2 D)
    nlinarith only [h, hNormSq]
  have hSmall' : shiftedResidualMass D k R < ‖(v : quotientL2 D)‖ ^ (2 : ℕ) := by
    simpa only [one_mul] using hSmall
  have hv : ‖T v - (lambda : ℂ) • (v : quotientL2 D)‖ ^ (2 : ℕ) <
      ‖(v : quotientL2 D)‖ ^ (2 : ℕ) := by
    have hCast : (lambda : ℂ) = -((1 / 4 + k ^ 2 : ℝ) : ℂ) := Complex.ofReal_neg _
    rw [hCast]
    exact (hResidual k R hR).trans_lt hSmall'
  refine ⟨v, hNormSq, ?_⟩
  exact (re_diagonal_lt_of_small_residual (v : quotientL2 D) (T v) lambda hNorm hv).trans
    (mul_lt_mul_of_pos_right hlambda hNormSq)

end
end ManuscriptAudit.Paper9SmoothWaveLowerBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9SmoothWaveLowerBound.test_diagonal_below_every_mass_multiple
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
