import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Function.L2Space
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoProfileIntegrability
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspWaveQuotientCoefficient

/-! The compact log-wave is a nonzero vector of the native measured
complex quotient (L^2), expressed in the unit theta frame. Its norm
agrees exactly with the quotient trial density used in the residual estimate. -/

namespace ManuscriptAudit.Paper9CuspWaveHilbert

open Filter Set MeasureTheory Paper9HighCuspSection Paper9SmoothCuspWave
open Paper9LogCuspWave Paper9QuotientCuspWave Paper9QuotientLogProfile Paper9CuspWaveBump
open Paper9CuspWaveQuotientCoefficient GammaTwoQuotientHeightIntegral GammaTwoProfileIntegrability
open Paper9CuspPotentialGlobal ThetaChosenQuotientAnalysis HyperbolicCuspGaugeTest
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry
open scoped UpperHalfPlane Topology InnerProductSpace

noncomputable section

private def massHeightProfile (k R y : ℝ) : ℝ := ‖chartAmplitude k R y‖ ^ (2 : ℕ) / y ^ (2 : ℕ)

private theorem continuous_massHeightProfile (k R : ℝ) (hR : 0 < R) :
    Continuous (massHeightProfile k R) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (Real.exp_pos R)] with t ht
    simp [massHeightProfile, chartAmplitude_zero_below k R t hR ht.le]
  · have hA : Continuous (fun t : ℝ => ‖chartAmplitude k R t‖ ^ (2 : ℕ)) :=
      (chartAmplitude_smooth k R hR).continuous.norm.pow 2
    have hD : Continuous (fun t : ℝ => t ^ (2 : ℕ)) := continuous_id.pow 2
    exact hA.continuousAt.div hD.continuousAt (pow_ne_zero 2 hy)

theorem unitThetaCoefficient_memLp (D : GammaTwoFundamentalDomain) (k R : ℝ) (hR : 0 < R) :
    MemLp (unitThetaCoefficient k R) 2 D.quotientMeasure := by
  have hTheta := (quotientDensity_integrable D).aemeasurable
  have hSqrt : AEMeasurable (fun q => Real.sqrt (quotientDensity q)) D.quotientMeasure :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hTheta
  have hCast : AEStronglyMeasurable (fun q => (Real.sqrt (quotientDensity q) : ℂ))
      D.quotientMeasure :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable hSqrt).aestronglyMeasurable
  have hCoeff : AEStronglyMeasurable (unitThetaCoefficient k R) D.quotientMeasure :=
    hCast.mul (quotientProfile_continuous k R hR).measurable.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hCoeff).mpr
  have hExp : 1 < Real.exp R := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hR
  have hLow : ∀ y ≤ 1, massHeightProfile k R y = 0 := by
    intro y hy
    simp [massHeightProfile, chartAmplitude_zero_below k R y hR (hy.trans hExp.le)]
  have hHigh : ∀ y > Real.exp (R * 6), massHeightProfile k R y = 0 := by
    intro y hy
    simp [massHeightProfile, chartAmplitude_zero_above k R y hR hy.le]
  have hI := integrable_quotient_profile D (massHeightProfile k R)
    (continuous_massHeightProfile k R hR) hLow hHigh
  apply hI.congr
  apply Eventually.of_forall
  intro q
  have hq : 0 < quotientHeight q := by
    obtain ⟨z, rfl⟩ := gammaTwoQuotientMk_isOpenQuotientMap.surjective q
    rw [quotientHeight_mk]
    exact z.im_pos.trans_le (orbitHeight_ge_im z)
  rw [unitThetaCoefficient_norm k R hR]
  unfold massHeightProfile
  field_simp [hq.ne'] <;> ring

abbrev quotientL2 (D : GammaTwoFundamentalDomain) := Lp ℂ 2 D.quotientMeasure

/-- The native quotient Hilbert-space vector of the compact cusp wave. -/
def waveVector (D : GammaTwoFundamentalDomain) (k R : ℝ) (hR : 0 < R) : quotientL2 D :=
  (unitThetaCoefficient_memLp D k R hR).toLp (unitThetaCoefficient k R)

theorem waveVector_norm_sq (D : GammaTwoFundamentalDomain) (k R : ℝ) (hR : 0 < R) :
    ‖waveVector D k R hR‖ ^ (2 : ℕ) =
      ∫ q, squaredDensity (trial cuspBump k R) (Real.exp R) (Real.exp (R * 6)) q
        ∂D.quotientMeasure := by
  let v := waveVector D k R hR
  have he : (v : GammaTwoQuotient → ℂ) =ᵐ[D.quotientMeasure] unitThetaCoefficient k R :=
    (unitThetaCoefficient_memLp D k R hR).coeFn_toLp
  have hI : Integrable (fun q => inner ℂ (v q) (v q)) D.quotientMeasure :=
    MeasureTheory.L2.integrable_inner v v
  change ‖v‖ ^ (2 : ℕ) = _
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def]
  change Complex.reCLM (∫ q, inner ℂ (v q) (v q) ∂D.quotientMeasure) = _
  rw [← Complex.reCLM.integral_comp_comm hI]
  apply integral_congr_ae
  filter_upwards [he] with q hq
  change (inner ℂ (v q) (v q)).re = _
  rw [hq, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact unitThetaCoefficient_norm_sq k R hR q

private theorem trialIntegral_pos (D : GammaTwoFundamentalDomain) (k R : ℝ) (hR : 0 < R) :
    0 < ∫ q, squaredDensity (trial cuspBump k R) (Real.exp R) (Real.exp (R * 6)) q
      ∂D.quotientMeasure := by
  have hExp : 1 < Real.exp R := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hR
  have hab : Real.exp R ≤ Real.exp (R * 6) := Real.exp_le_exp.mpr (by linarith)
  have hTrial : Continuous (fun t => ‖trial cuspBump k R t‖ ^ (2 : ℕ)) :=
    (trial_smooth cuspBump cuspBump_smooth k R).continuous.norm.pow 2
  have hMass : 0 < Paper9LogCuspWaveMass.mass cuspBump 1 6 := by
    have h : 0 < 2 * Paper9LogCuspWaveMass.mass cuspBump 1 6 := cuspMass_pos
    linarith only [h]
  unfold squaredDensity
  rw [integral_density D _ hTrial hExp hab, Real.log_exp, Real.log_exp]
  have h := Paper9LogCuspWaveMass.trial_mass cuspBump 1 6 k R hR.ne'
  rw [mul_one] at h
  rw [h]
  exact mul_pos zero_lt_two (mul_pos hR hMass)

/-- A smooth compactly supported genuine quotient test section has
positive (L^2) mass and arbitrarily small measured shifted residual
relative to that mass. The derivative identification is
`Paper9SmoothCuspWave.densities_on_high_slab`. -/
theorem exists_smooth_compact_wave_small_residual (D : GammaTwoFundamentalDomain)
    (k : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : ℝ) (hR : 1 ≤ R),
      RealSmooth (extendedSection (chartAmplitude k R)) ∧
      HasQuotientCompactSupport (extendedSection (chartAmplitude k R)) ∧
      0 < ‖waveVector D k R (zero_lt_one.trans_le hR)‖ ^ (2 : ℕ) ∧
      (∫ q, squaredDensity (residual (deriv cuspBump) (deriv (deriv cuspBump)) k R)
        (Real.exp R) (Real.exp (R * 6)) q ∂D.quotientMeasure) <
        ε * ‖waveVector D k R (zero_lt_one.trans_le hR)‖ ^ (2 : ℕ) := by
  obtain ⟨R, hR, hRes⟩ := exists_small_residual_of_cuspBump D k hε
  have hR' := zero_lt_one.trans_le hR
  refine ⟨R, hR, (smooth_and_compact_section k R hR').1,
    section_quotientCompact k R hR', ?_, ?_⟩
  · rw [waveVector_norm_sq]
    exact trialIntegral_pos D k R hR'
  · rw [waveVector_norm_sq]
    exact hRes

end
end ManuscriptAudit.Paper9CuspWaveHilbert

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspWaveHilbert.unitThetaCoefficient_memLp,
      ``ManuscriptAudit.Paper9CuspWaveHilbert.waveVector_norm_sq,
      ``ManuscriptAudit.Paper9CuspWaveHilbert.exists_smooth_compact_wave_small_residual] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
