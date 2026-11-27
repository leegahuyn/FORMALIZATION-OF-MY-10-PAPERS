import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9LogCuspWaveMass
import PrimalitySheafVerification.ManuscriptAudit.Paper9QuotientLogProfile

/-! Approximate critical modes measured in the genuine width-two quotient cusp. -/

namespace ManuscriptAudit.Paper9QuotientCuspWave

open Set MeasureTheory Paper9LogCuspWave Paper9LogCuspWaveMass
open Paper9CuspLogTransform Paper9CuspLogMass GammaTwoQuotientHeightIntegral
open Paper9HighCuspSection Paper9HighCuspCoordinates Paper9PrintedLaplacianSign
open Paper9QuotientLogProfile
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane

noncomputable section

def squaredDensity (g : ℝ → ℂ) (a b : ℝ) (q : GammaTwoQuotient) : ℝ :=
  density (fun t => ‖g t‖ ^ (2 : ℕ)) a b q

theorem squaredDensity_on_slab (g : ℝ → ℂ) {a b : ℝ} (ha : 1 < a)
    (z : ℍ) (hz : z.im ∈ Ioc a b) :
    squaredDensity g a b (gammaTwoQuotientMk z) = ‖weightedLogProfile g z.im‖ ^ (2 : ℕ) := by
  have h := quotientHeight_high z (ha.trans hz.1).le
  unfold squaredDensity
  rw [density_at_height _ (show quotientHeight (gammaTwoQuotientMk z) ∈ Ioc a b by rwa [h])
    (show 0 < quotientHeight (gammaTwoQuotientMk z) by rw [h]; exact z.im_pos),
    h, weightedLogProfile_norm_sq g z.im_pos]

theorem trialDensity_on_slab (b : ℝ → ℝ) (k R : ℝ) {a d : ℝ} (ha : 1 < a)
    (z : ℍ) (hz : z.im ∈ Ioc a d) :
    squaredDensity (trial b k R) a d (gammaTwoQuotientMk z) =
      ‖extendedSection (weightedLogProfile (trial b k R)) z‖ ^ (2 : ℕ) := by
  rw [squaredDensity_on_slab _ ha z hz, extendedSection_at_high _ z (ha.trans hz.1)]

theorem residualDensity_on_slab (b b' b'' : ℝ → ℝ) (k R : ℝ)
    (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : ∀ t, HasDerivAt b' (b'' t) t)
    {a d : ℝ} (ha : 1 < a) (z : ℍ) (hz : z.im ∈ Ioc a d) :
    squaredDensity (residual b' b'' k R) a d (gammaTwoQuotientMk z) =
      ‖printedL (coordinates (weightedLogProfile (trial b k R))) z -
        (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) * extendedSection (weightedLogProfile (trial b k R)) z‖ ^
        (2 : ℕ) := by
  have hDiff : Differentiable ℝ (trial b k R) :=
    fun t => (trial_hasDerivAt b b' k R t hb).differentiableAt
  have hEq : deriv (trial b k R) = trialDeriv b b' k R :=
    funext (fun t => (trial_hasDerivAt b b' k R t hb).deriv)
  have hDiff' : Differentiable ℝ (deriv (trial b k R)) := by
    rw [hEq]
    exact fun t => (trialDeriv_hasDerivAt b b' b'' k R t hb hb').differentiableAt
  have hHigh : 1 < z.im := ha.trans hz.1
  rw [squaredDensity_on_slab _ ha z hz, printedL_weightedLogProfile _ hDiff hDiff' z hHigh,
    extendedSection_at_high _ z hHigh]
  have hValue (t : ℝ) :
      deriv (deriv (trial b k R)) t - (1 / 4 : ℂ) * trial b k R t -
        (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) * trial b k R t = residual b' b'' k R t :=
    shifted_mode_residual b b' b'' k R t hb hb'
  unfold weightedLogProfile
  rw [← hValue (Real.log z.im)]
  congr 2
  ring

private theorem residual_continuous (b' b'' : ℝ → ℝ) (k R : ℝ)
    (hB : Continuous b') (hC : Continuous b'') : Continuous (residual b' b'' k R) := by
  have hScale : Continuous (fun t : ℝ => t / R) := continuous_id.div_const R
  have hA (b : ℝ → ℝ) (hb : Continuous b) : Continuous (amplitude b R) :=
    Complex.continuous_ofReal.comp (hb.comp hScale)
  have hP : Continuous (phase k) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact (((hA b'' hC).mul continuous_const).add
    ((continuous_const.mul (hA b' hB)).mul continuous_const)).mul hP

/-- The measured quotient residual divided by the measured wave mass is the
corresponding logarithmic profile quotient at every positive scale. -/
theorem quotient_relative_eq (D : GammaTwoFundamentalDomain)
    (b b' b'' : ℝ → ℝ) (k R : ℝ) (hR : 0 < R)
    (hb : ∀ t, HasDerivAt b (b' t) t) (hB : Continuous b')
    (hC : Continuous b'') (hM : mass b 1 6 ≠ 0) :
    (∫ q, squaredDensity (residual b' b'' k R) (Real.exp R) (Real.exp (R * 6)) q
      ∂D.quotientMeasure) /
    (∫ q, squaredDensity (trial b k R) (Real.exp R) (Real.exp (R * 6)) q
      ∂D.quotientMeasure) = relativeResidual b b' b'' 1 6 k R := by
  have ha : 1 < Real.exp R := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hR
  have hab : Real.exp R ≤ Real.exp (R * 6) := Real.exp_le_exp.mpr (by linarith)
  have hTrial : Continuous (trial b k R) :=
    continuous_iff_continuousAt.mpr (fun t => (trial_hasDerivAt b b' k R t hb).continuousAt)
  have hResSq : Continuous (fun t => ‖residual b' b'' k R t‖ ^ (2 : ℕ)) :=
    (residual_continuous b' b'' k R hB hC).norm.fun_pow 2
  have hTrialSq : Continuous (fun t => ‖trial b k R t‖ ^ (2 : ℕ)) := hTrial.norm.fun_pow 2
  unfold squaredDensity
  rw [integral_density D _ hResSq ha hab, integral_density D _ hTrialSq ha hab,
    Real.log_exp, Real.log_exp]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simpa only [mul_one] using relative_eq b b' b'' 1 6 k R hR.ne' hB hC hM

theorem exists_small_quotient_residual (D : GammaTwoFundamentalDomain)
    (b b' b'' : ℝ → ℝ) (k : ℝ) (hb : ∀ t, HasDerivAt b (b' t) t)
    (hB : Continuous b') (hC : Continuous b'') (hM : 0 < mass b 1 6)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      (∫ q, squaredDensity (residual b' b'' k R) (Real.exp R) (Real.exp (R * 6)) q
        ∂D.quotientMeasure) <
        ε * (∫ q, squaredDensity (trial b k R) (Real.exp R) (Real.exp (R * 6)) q
          ∂D.quotientMeasure) := by
  obtain ⟨R, hR, hI⟩ := exists_small_relative_residual b b' b'' 1 6 k hB hC hM hε
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have ha : 1 < Real.exp R := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hR0
  have hab : Real.exp R ≤ Real.exp (R * 6) := Real.exp_le_exp.mpr (by linarith)
  have hTrial : Continuous (trial b k R) :=
    continuous_iff_continuousAt.mpr (fun t => (trial_hasDerivAt b b' k R t hb).continuousAt)
  refine ⟨R, hR, ?_⟩
  unfold squaredDensity
  have hResSq : Continuous (fun t => ‖residual b' b'' k R t‖ ^ (2 : ℕ)) :=
    (residual_continuous b' b'' k R hB hC).norm.fun_pow 2
  have hTrialSq : Continuous (fun t => ‖trial b k R t‖ ^ (2 : ℕ)) := hTrial.norm.fun_pow 2
  rw [integral_density D (fun t => ‖residual b' b'' k R t‖ ^ (2 : ℕ)) hResSq ha hab,
    integral_density D (fun t => ‖trial b k R t‖ ^ (2 : ℕ)) hTrialSq ha hab]
  simp only [Real.log_exp, mul_one] at hI ⊢
  linarith only [hI]

end
end ManuscriptAudit.Paper9QuotientCuspWave

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9QuotientCuspWave.squaredDensity_on_slab,
      ``ManuscriptAudit.Paper9QuotientCuspWave.trialDensity_on_slab,
      ``ManuscriptAudit.Paper9QuotientCuspWave.residualDensity_on_slab,
      ``ManuscriptAudit.Paper9QuotientCuspWave.quotient_relative_eq,
      ``ManuscriptAudit.Paper9QuotientCuspWave.exists_small_quotient_residual] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
