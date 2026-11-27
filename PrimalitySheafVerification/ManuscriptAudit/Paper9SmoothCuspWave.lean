import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspSectionSmooth
import PrimalitySheafVerification.ManuscriptAudit.Paper9ArbitraryHeightSupport
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspWaveBump

/-! The concrete logarithmic wave defines a smooth theta-multiplier
section with compact quotient support. Clipping to positive high
heights leaves the function zero on a neighborhood of the seam. -/

namespace ManuscriptAudit.Paper9SmoothCuspWave

open Filter Set Paper9HighCuspSection Paper9LogCuspWave Paper9CuspLogTransform
open Paper9ArbitraryHeightSupport Paper9CuspWaveBump HyperbolicCuspGaugeTest
open Paper9HighCuspCoordinates Paper9PrintedLaplacianSign Paper9QuotientCuspWave
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped ContDiff UpperHalfPlane Topology

noncomputable section

private theorem complexMul_real_smooth :
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2) :=
  (contDiff_mul : ContDiff ℂ ∞ (fun p : ℂ × ℂ => p.1 * p.2)).restrict_scalars ℝ

theorem trial_smooth (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (k R : ℝ) :
    ContDiff ℝ ∞ (trial b k R) := by
  have hScale : ContDiff ℝ ∞ (fun t : ℝ => t / R) := contDiff_id.div_const R
  have hAmp : ContDiff ℝ ∞ (amplitude b R) :=
    Complex.ofRealCLM.contDiff.comp (hb.comp hScale)
  let G : ℂ → ℂ := fun w => Complex.exp (w * frequency k)
  have hG : ContDiff ℂ ∞ G := (contDiff_id.mul contDiff_const).cexp
  have hPhase : ContDiff ℝ ∞ (phase k) :=
    (hG.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  exact complexMul_real_smooth.comp (hAmp.prodMk hPhase)

private theorem weighted_profile_smoothAt (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (weightedLogProfile g) y := by
  have hPow : ContDiffAt ℝ ∞ (fun y : ℝ => y ^ (1 / 2 : ℝ)) y :=
    contDiffAt_rpow_const_of_ne hy.ne'
  have hCast : ContDiffAt ℝ ∞ (fun y : ℝ => ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y hPow
  have hLog : ContDiffAt ℝ ∞ Real.log y := Real.contDiffAt_log.mpr hy.ne'
  have hG : ContDiffAt ℝ ∞ (fun t => g (Real.log t)) y :=
    hg.contDiffAt.comp y hLog
  exact complexMul_real_smooth.contDiffAt.comp y (hCast.prodMk hG)

/-- The real-height amplitude of the compactly supported wave. -/
def chartAmplitude (k R y : ℝ) : ℂ :=
  if 1 < y then weightedLogProfile (trial cuspBump k R) y else 0

theorem chartAmplitude_high (k R : ℝ) {y : ℝ} (hy : 1 < y) :
    chartAmplitude k R y = weightedLogProfile (trial cuspBump k R) y :=
  if_pos hy

private theorem chartAmplitude_zero_logOutside (k R y : ℝ) (hR : 0 < R)
    (h : Real.log y ≤ R ∨ R * 6 ≤ Real.log y) : chartAmplitude k R y = 0 := by
  by_cases hy : 1 < y
  · rw [chartAmplitude_high k R hy, weightedLogProfile,
      (zero_outside_log_slab k R (Real.log y) hR h).1, mul_zero]
  · exact if_neg hy

theorem chartAmplitude_zero_below (k R y : ℝ) (hR : 0 < R) (hy : y ≤ Real.exp R) :
    chartAmplitude k R y = 0 := by
  by_cases h : 1 < y
  · have hLog := Real.log_le_log (zero_lt_one.trans h) hy
    rw [Real.log_exp] at hLog
    exact chartAmplitude_zero_logOutside k R y hR (Or.inl hLog)
  · exact if_neg h

theorem chartAmplitude_zero_above (k R y : ℝ) (hR : 0 < R) (hy : Real.exp (R * 6) ≤ y) :
    chartAmplitude k R y = 0 := by
  have h := Real.log_le_log (Real.exp_pos (R * 6)) hy
  rw [Real.log_exp] at h
  exact chartAmplitude_zero_logOutside k R y hR (Or.inr h)

theorem chartAmplitude_smooth (k R : ℝ) (hR : 0 < R) : ContDiff ℝ ∞ (chartAmplitude k R) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 1 < y
  · apply (weighted_profile_smoothAt _ (trial_smooth _ cuspBump_smooth k R)
      (zero_lt_one.trans hy)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact chartAmplitude_high k R ht
  · have hExp : 1 < Real.exp R := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hR
    have hNear : y < Real.exp R := (le_of_not_gt hy).trans_lt hExp
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) y).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hNear] with t ht
    exact chartAmplitude_zero_below k R t hR ht.le

private theorem chartAmplitude_zero_outside (k R : ℝ) (hR : 0 < R) :
    ∀ y, y < Real.exp R ∨ Real.exp (R * 6) < y → chartAmplitude k R y = 0 := by
  rintro y (hy | hy)
  · exact chartAmplitude_zero_below k R y hR hy.le
  · exact chartAmplitude_zero_above k R y hR hy.le

/-- Smoothness upstairs and compact support on the actual quotient. -/
theorem smooth_and_compact_section (k R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (fun w => extendedSection (chartAmplitude k R) (UpperHalfPlane.ofComplex w))
      UpperHalfPlane.upperHalfPlaneSet ∧ HasCompactSupport (quotientProfile (chartAmplitude k R)) := by
  let K := gammaTwoQuotientMk '' closedHeightStrip (Real.exp R) (Real.exp (R * 6))
  have hK : IsCompact K := (closedHeightStrip_compact (Real.exp_pos R)).image
    gammaTwoQuotientMk_isOpenQuotientMap.continuous
  have hSupport : Function.support (quotientProfile (chartAmplitude k R)) ⊆ K :=
    support_subset_quotient_strip _ (chartAmplitude_zero_outside k R hR)
  have hExp : 1 < Real.exp R := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hR
  refine ⟨extendedSection_realSmooth_of_closed_support _ (chartAmplitude_smooth k R)
    K hK.isClosed ?_ hSupport, profile_compact_support _ (Real.exp_pos R)
      (chartAmplitude_zero_outside k R hR)⟩
  rintro q ⟨z, hz, rfl⟩
  exact ⟨z, hExp.trans_le hz.2.1, rfl⟩

theorem section_at_high (k R : ℝ) (z : ℍ) (hz : 1 < z.im) :
    extendedSection (chartAmplitude k R) z =
      extendedSection (weightedLogProfile (trial cuspBump k R)) z := by
  rw [extendedSection_at_high _ z hz, extendedSection_at_high _ z hz, chartAmplitude_high k R hz]

/-- The clipped section has the identical printed differential expression
as the logarithmic wave on the high cusp. -/
theorem printedL_at_high (k R : ℝ) (z : ℍ) (hz : 1 < z.im) :
    printedL (coordinates (chartAmplitude k R)) z =
      printedL (coordinates (weightedLogProfile (trial cuspBump k R))) z := by
  have he : chartAmplitude k R =ᶠ[𝓝 z.im] weightedLogProfile (trial cuspBump k R) := by
    filter_upwards [Ioi_mem_nhds hz] with y hy
    exact chartAmplitude_high k R hy
  rw [printedL_high _ z hz, printedL_high _ z hz, he.deriv.deriv_eq]

/-- On every high slab these densities are exactly the mass and
shifted differential residual of the genuine smooth section. -/
theorem densities_on_high_slab (k R : ℝ) {a d : ℝ} (ha : 1 < a)
    (z : ℍ) (hz : z.im ∈ Ioc a d) :
    squaredDensity (trial cuspBump k R) a d (gammaTwoQuotientMk z) =
        ‖extendedSection (chartAmplitude k R) z‖ ^ (2 : ℕ) ∧
      squaredDensity (residual (deriv cuspBump) (deriv (deriv cuspBump)) k R)
        a d (gammaTwoQuotientMk z) =
        ‖printedL (coordinates (chartAmplitude k R)) z -
          (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) * extendedSection (chartAmplitude k R) z‖ ^ (2 : ℕ) := by
  have hHigh := ha.trans hz.1
  have hB : ContDiff ℝ 1 cuspBump := contDiff_infty.mp cuspBump_smooth 1
  have hC : ContDiff ℝ (1 + 1) cuspBump := contDiff_infty.mp cuspBump_smooth 2
  have hD : ContDiff ℝ 1 (deriv cuspBump) := (contDiff_succ_iff_deriv.mp hC).2.2
  constructor
  · rw [trialDensity_on_slab cuspBump k R ha z hz, section_at_high k R z hHigh]
  · rw [residualDensity_on_slab cuspBump (deriv cuspBump) (deriv (deriv cuspBump)) k R
      (fun t => ((hB.differentiable (by decide)) t).hasDerivAt)
      (fun t => ((hD.differentiable (by decide)) t).hasDerivAt) ha z hz,
      printedL_at_high k R z hHigh, section_at_high k R z hHigh]

end
end ManuscriptAudit.Paper9SmoothCuspWave

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9SmoothCuspWave.trial_smooth,
      ``ManuscriptAudit.Paper9SmoothCuspWave.chartAmplitude_smooth,
      ``ManuscriptAudit.Paper9SmoothCuspWave.smooth_and_compact_section,
      ``ManuscriptAudit.Paper9SmoothCuspWave.printedL_at_high,
      ``ManuscriptAudit.Paper9SmoothCuspWave.densities_on_high_slab] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
