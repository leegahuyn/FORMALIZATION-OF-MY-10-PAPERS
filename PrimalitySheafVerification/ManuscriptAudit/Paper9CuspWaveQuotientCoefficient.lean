import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9SmoothCuspWave

/-! The log-cusp wave has a concrete quotient coefficient in the
unit theta frame. Its magnitude is exactly the magnitude of the
smooth unitary section at every representative. -/

namespace ManuscriptAudit.Paper9CuspWaveQuotientCoefficient

open Set MeasureTheory Paper9HighCuspSection Paper9SmoothCuspWave Paper9QuotientCuspWave
open Paper9LogCuspWave Paper9CuspLogTransform Paper9CuspLogMass Paper9QuotientLogProfile
open ThetaGlobalSection ThetaChosenQuotientAnalysis GammaTwoQuotientHeightIntegral
open Paper9CuspPotentialGlobal HyperbolicCuspGaugeTest
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open Mock2FA.PaperCorrections.AutomorphicSobolev.SmoothCompactCoreGeometry
open scoped UpperHalfPlane

noncomputable section

private theorem continuous_theta_mode : Continuous thetaWeightedMode := by
  have hTheta : Continuous (fun z : ℍ => jacobiTheta (z : ℂ)) := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    exact ContinuousAt.comp' (f := UpperHalfPlane.coe) (x := z)
      (continuousAt_jacobiTheta z.im_pos) UpperHalfPlane.continuous_coe.continuousAt
  have hPow : Continuous (fun z : ℍ => z.im ^ (1 / 4 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num)).comp UpperHalfPlane.continuous_im
  exact (Complex.continuous_ofReal.comp hPow).mul hTheta

theorem quotientProfile_continuous (k R : ℝ) (hR : 0 < R) :
    Continuous (quotientProfile (chartAmplitude k R)) := by
  let a := chartAmplitude k R
  have hSmooth : RealSmooth (extendedSection a) := (smooth_and_compact_section k R hR).1
  apply gammaTwoQuotientMk_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  have hDiv : Continuous (fun z : ℍ => extendedSection a z / thetaWeightedMode z) :=
    hSmooth.continuous.div continuous_theta_mode thetaWeightedMode_ne_zero
  have he : (quotientProfile a) ∘ gammaTwoQuotientMk =
      fun z : ℍ => extendedSection a z / thetaWeightedMode z := by
    funext z
    change quotientProfile a (gammaTwoQuotientMk z) = _
    rw [extendedSection, mul_comm, mul_div_cancel_right₀ _ (thetaWeightedMode_ne_zero z)]
  rw [he]
  exact hDiv

theorem section_quotientCompact (k R : ℝ) (hR : 0 < R) :
    HasQuotientCompactSupport (extendedSection (chartAmplitude k R)) := by
  let a := chartAmplitude k R
  have he : gammaTwoQuotientMk '' Function.support (extendedSection a) =
      Function.support (quotientProfile a) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩ hzero
      apply hz
      rw [extendedSection, hzero, mul_zero]
    · intro hq
      obtain ⟨z, rfl⟩ := gammaTwoQuotientMk_isOpenQuotientMap.surjective q
      exact ⟨z, mul_ne_zero (thetaWeightedMode_ne_zero z) hq, rfl⟩
  change IsCompact (closure (gammaTwoQuotientMk '' Function.support (extendedSection a)))
  rw [he]
  exact (smooth_and_compact_section k R hR).2

/-- Scalar coefficient of the wave in the unit frame supplied by the
nonvanishing theta mode. The frame has the manuscript's unitary phase. -/
def unitThetaCoefficient (k R : ℝ) (q : GammaTwoQuotient) : ℂ :=
  (Real.sqrt (quotientDensity q) : ℂ) * quotientProfile (chartAmplitude k R) q

theorem unitThetaCoefficient_represents (k R : ℝ) (z : ℍ) :
    (thetaWeightedMode z / (‖thetaWeightedMode z‖ : ℂ)) *
        unitThetaCoefficient k R (gammaTwoQuotientMk z) =
      extendedSection (chartAmplitude k R) z := by
  have hNorm : (‖thetaWeightedMode z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr (thetaWeightedMode_ne_zero z)).ne'
  rw [unitThetaCoefficient, quotientDensity_pullback, Real.sqrt_sq (norm_nonneg _),
    ← mul_assoc, div_mul_cancel₀ _ hNorm, extendedSection]

theorem unitThetaCoefficient_norm_at_mk (k R : ℝ) (z : ℍ) :
    ‖unitThetaCoefficient k R (gammaTwoQuotientMk z)‖ =
      ‖extendedSection (chartAmplitude k R) z‖ := by
  rw [unitThetaCoefficient, quotientDensity_pullback, Real.sqrt_sq (norm_nonneg _),
    extendedSection, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

private theorem quotientHeight_pos (q : GammaTwoQuotient) : 0 < quotientHeight q := by
  obtain ⟨z, rfl⟩ := gammaTwoQuotientMk_isOpenQuotientMap.surjective q
  rw [quotientHeight_mk]
  exact z.im_pos.trans_le (orbitHeight_ge_im z)

theorem unitThetaCoefficient_norm (k R : ℝ) (hR : 0 < R) (q : GammaTwoQuotient) :
    ‖unitThetaCoefficient k R q‖ = ‖chartAmplitude k R (quotientHeight q)‖ := by
  by_cases hHigh : 1 < quotientHeight q
  · obtain ⟨z, hz, rfl⟩ := mem_strip_image_of_height hHigh
    have hz' : 1 < z.im := hz.1
    rw [unitThetaCoefficient_norm_at_mk, extendedSection_at_high _ z hz',
      quotientHeight_high z hz'.le]
  · have hFail : ¬ ∃ z : ℍ, gammaTwoQuotientMk z = q ∧ 1 < z.im := by
      rintro ⟨z, rfl, hz⟩
      exact hHigh (by rwa [quotientHeight_high z hz.le])
    have hZero : quotientProfile (chartAmplitude k R) q = 0 := by
      unfold quotientProfile
      split
      next hExists =>
        exact (hFail (show ∃ z : ℍ, gammaTwoQuotientMk z = q ∧ 1 < z.im from hExists)).elim
      next => rfl
    have hExp : 1 < Real.exp R := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hR
    rw [unitThetaCoefficient, hZero, mul_zero,
      chartAmplitude_zero_below k R _ hR ((le_of_not_gt hHigh).trans hExp.le)]

/-- The density is the actual norm square everywhere on the quotient. -/
theorem unitThetaCoefficient_norm_sq (k R : ℝ) (hR : 0 < R) (q : GammaTwoQuotient) :
    ‖unitThetaCoefficient k R q‖ ^ (2 : ℕ) =
      squaredDensity (trial cuspBump k R) (Real.exp R) (Real.exp (R * 6)) q := by
  rw [unitThetaCoefficient_norm k R hR]
  have hExp : 1 < Real.exp R := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hR
  by_cases hSlab : quotientHeight q ∈ Ioc (Real.exp R) (Real.exp (R * 6))
  · rw [chartAmplitude_high k R (hExp.trans hSlab.1),
      weightedLogProfile_norm_sq _ (quotientHeight_pos q), squaredDensity,
      density_at_height _ hSlab (quotientHeight_pos q)]
  · have hZero : chartAmplitude k R (quotientHeight q) = 0 := by
      by_cases hLow : Real.exp R < quotientHeight q
      · exact chartAmplitude_zero_above k R _ hR
          (lt_of_not_ge (fun h => hSlab ⟨hLow, h⟩)).le
      · exact chartAmplitude_zero_below k R _ hR (le_of_not_gt hLow)
    simp [hZero, squaredDensity, density, clipped, hSlab]

end
end ManuscriptAudit.Paper9CuspWaveQuotientCoefficient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspWaveQuotientCoefficient.quotientProfile_continuous,
      ``ManuscriptAudit.Paper9CuspWaveQuotientCoefficient.section_quotientCompact,
      ``ManuscriptAudit.Paper9CuspWaveQuotientCoefficient.unitThetaCoefficient_represents,
      ``ManuscriptAudit.Paper9CuspWaveQuotientCoefficient.unitThetaCoefficient_norm_sq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
