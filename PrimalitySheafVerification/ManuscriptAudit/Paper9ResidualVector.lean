import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspWaveHilbert

/-! The exact shifted cusp differential has a vector in the native quotient L². -/

namespace ManuscriptAudit.Paper9ResidualVector

open Filter Set MeasureTheory
open Paper9CuspLogTransform Paper9CuspLogMass Paper9CuspWaveHilbert Paper9CuspWaveBump
open Paper9LogCuspWave Paper9QuotientCuspWave Paper9QuotientLogProfile HyperbolicCuspGaugeTest
open GammaTwoQuotientHeightIntegral GammaTwoProfileIntegrability Paper9CuspPotentialGlobal
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open Paper9HighCuspSection Paper9HighCuspCoordinates Paper9PrintedLaplacianSign
open Paper9SmoothCuspWave
open scoped Topology UpperHalfPlane

noncomputable section

abbrev logResidual (k R : ℝ) : ℝ → ℂ :=
  residual (deriv cuspBump) (deriv (deriv cuspBump)) k R

def residualCoefficient (k R : ℝ) (q : GammaTwoQuotient) : ℂ :=
  weightedLogProfile (logResidual k R) (quotientHeight q)

/-- On the actual high cusp, the coefficient equals the shifted printed differential. -/
theorem residualCoefficient_at_high (k R : ℝ) (z : ℍ) (hz : 1 < z.im) :
    residualCoefficient k R (gammaTwoQuotientMk z) =
      printedL (coordinates (chartAmplitude k R)) z -
        (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) * extendedSection (chartAmplitude k R) z := by
  have h₁ : ContDiff ℝ 1 cuspBump := contDiff_infty.mp cuspBump_smooth 1
  have h₂ : ContDiff ℝ (1 + 1) cuspBump := contDiff_infty.mp cuspBump_smooth 2
  have hd : ContDiff ℝ 1 (deriv cuspBump) := (contDiff_succ_iff_deriv.mp h₂).2.2
  let g := trial cuspBump k R
  have hb (t : ℝ) : HasDerivAt cuspBump (deriv cuspBump t) t :=
    ((h₁.differentiable (by decide)) t).hasDerivAt
  have hb' (t : ℝ) : HasDerivAt (deriv cuspBump) (deriv (deriv cuspBump) t) t :=
    ((hd.differentiable (by decide)) t).hasDerivAt
  have hD : Differentiable ℝ g :=
    fun t => (trial_hasDerivAt _ _ k R t hb).differentiableAt
  have hEq : deriv g = trialDeriv cuspBump (deriv cuspBump) k R :=
    funext (fun t => (trial_hasDerivAt _ _ k R t hb).deriv)
  have hD' : Differentiable ℝ (deriv g) := by
    rw [hEq]
    exact fun t => (trialDeriv_hasDerivAt _ _ _ k R t hb hb').differentiableAt
  rw [residualCoefficient, quotientHeight_high z hz.le, printedL_at_high k R z hz,
    printedL_weightedLogProfile g hD hD' z hz, section_at_high k R z hz,
    extendedSection_at_high _ z hz]
  have hValue := shifted_mode_residual cuspBump (deriv cuspBump) (deriv (deriv cuspBump))
    k R (Real.log z.im) hb hb'
  unfold weightedLogProfile logResidual
  rw [← hValue]
  ring

private theorem height_pos (q : GammaTwoQuotient) : 0 < quotientHeight q := by
  obtain ⟨z, rfl⟩ := gammaTwoQuotientMk_isOpenQuotientMap.surjective q
  rw [quotientHeight_mk]
  exact z.im_pos.trans_le (orbitHeight_ge_im z)

private theorem residual_zero_outside (k R y : ℝ) (hR : 0 < R) (hy : 0 < y)
    (hout : y ≤ Real.exp R ∨ Real.exp (R * 6) ≤ y) :
    logResidual k R (Real.log y) = 0 := by
  apply (zero_outside_log_slab k R (Real.log y) hR ?_).2
  rcases hout with h | h
  · exact Or.inl (by simpa only [Real.log_exp] using Real.log_le_log hy h)
  · exact Or.inr (by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) h)

private theorem continuous_logResidual (k R : ℝ) : Continuous (logResidual k R) := by
  have h₁ : ContDiff ℝ 1 cuspBump := contDiff_infty.mp cuspBump_smooth 1
  have h₂ : ContDiff ℝ (1 + 1) cuspBump := contDiff_infty.mp cuspBump_smooth 2
  have hd : ContDiff ℝ 1 (deriv cuspBump) := (contDiff_succ_iff_deriv.mp h₂).2.2
  exact residual_continuous _ _ k R h₁.continuous_deriv_one hd.continuous_deriv_one

private theorem clipped_eq_positive (k R y : ℝ) (hR : 0 < R) (hy : 0 < y) :
    clipped (fun t => ‖logResidual k R t‖ ^ (2 : ℕ)) (Real.exp R) (Real.exp (R * 6)) y =
      ‖logResidual k R (Real.log y)‖ ^ (2 : ℕ) * y⁻¹ := by
  by_cases hs : y ∈ Ioc (Real.exp R) (Real.exp (R * 6))
  · exact indicator_of_mem hs _
  · have hout : y ≤ Real.exp R ∨ Real.exp (R * 6) ≤ y := by
      by_cases ha : Real.exp R < y
      · exact Or.inr (lt_of_not_ge (fun hb => hs ⟨ha, hb⟩)).le
      · exact Or.inl (le_of_not_gt ha)
    rw [clipped, indicator_of_notMem hs, residual_zero_outside k R y hR hy hout, norm_zero]
    simp

private theorem continuous_clipped (k R : ℝ) (hR : 0 < R) :
    Continuous (clipped (fun t => ‖logResidual k R t‖ ^ (2 : ℕ))
      (Real.exp R) (Real.exp (R * 6))) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : 0 < y
  · have hLog : ContinuousAt Real.log y := Real.continuousAt_log hy.ne'
    have hG : ContinuousAt (fun t => ‖logResidual k R (Real.log t)‖ ^ (2 : ℕ)) y :=
      ((continuous_logResidual k R).norm.fun_pow 2).continuousAt.comp hLog
    have hInv : ContinuousAt (fun t : ℝ => t⁻¹) y := continuousAt_id.inv₀ hy.ne'
    apply (hG.mul hInv).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact clipped_eq_positive k R t hR ht
  · have hy' : y < Real.exp R := (le_of_not_gt hy).trans_lt (Real.exp_pos R)
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) y).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hy'] with t ht
    exact indicator_of_notMem (fun hs : t ∈ Ioc (Real.exp R) (Real.exp (R * 6)) =>
      (not_lt_of_ge ht.le) hs.1) _

theorem residualCoefficient_norm_sq (k R : ℝ) (hR : 0 < R) (q : GammaTwoQuotient) :
    ‖residualCoefficient k R q‖ ^ (2 : ℕ) =
      squaredDensity (logResidual k R) (Real.exp R) (Real.exp (R * 6)) q := by
  have hq := height_pos q
  unfold residualCoefficient squaredDensity density
  rw [weightedLogProfile_norm_sq _ hq, clipped_eq_positive k R _ hR hq]
  field_simp [hq.ne'] <;> ring

theorem residualCoefficient_memLp (D : GammaTwoFundamentalDomain) (k R : ℝ) (hR : 0 < R) :
    MemLp (residualCoefficient k R) 2 D.quotientMeasure := by
  have hLog : Measurable (fun y : ℝ => (Real.log y : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp Real.measurable_log
  have hPow : Measurable (Paper9EisensteinHeightEquation.heightPower (1 / 2)) :=
    Complex.continuous_exp.measurable.comp (hLog.mul_const _)
  have hF : Measurable (residualCoefficient k R) :=
    (hPow.mul ((continuous_logResidual k R).measurable.comp Real.measurable_log)).comp
      quotientHeight_measurable
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  let f := clipped (fun t => ‖logResidual k R t‖ ^ (2 : ℕ)) (Real.exp R) (Real.exp (R * 6))
  have hExp : 1 < Real.exp R := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hR
  have hLow (y : ℝ) (hy : y ≤ 1) : f y = 0 :=
    indicator_of_notMem (fun hs : y ∈ Ioc (Real.exp R) (Real.exp (R * 6)) =>
      (not_lt_of_ge (hy.trans hExp.le)) hs.1) _
  have hHigh (y : ℝ) (hy : Real.exp (R * 6) < y) : f y = 0 :=
    indicator_of_notMem (fun hs : y ∈ Ioc (Real.exp R) (Real.exp (R * 6)) =>
      (not_le_of_gt hy) hs.2) _
  exact (integrable_quotient_profile D f (continuous_clipped k R hR) hLow hHigh).congr
    (Eventually.of_forall (fun q => (residualCoefficient_norm_sq k R hR q).symm))

def residualVector (D : GammaTwoFundamentalDomain) (k R : ℝ) (hR : 0 < R) : quotientL2 D :=
  (residualCoefficient_memLp D k R hR).toLp (residualCoefficient k R)

theorem residualVector_norm_sq (D : GammaTwoFundamentalDomain) (k R : ℝ) (hR : 0 < R) :
    ‖residualVector D k R hR‖ ^ (2 : ℕ) =
      ∫ q, squaredDensity (logResidual k R) (Real.exp R) (Real.exp (R * 6)) q
        ∂D.quotientMeasure := by
  let v := residualVector D k R hR
  have he : (v : GammaTwoQuotient → ℂ) =ᵐ[D.quotientMeasure] residualCoefficient k R :=
    (residualCoefficient_memLp D k R hR).coeFn_toLp
  have hI : Integrable (fun q => inner ℂ (v q) (v q)) D.quotientMeasure :=
    MeasureTheory.L2.integrable_inner v v
  change ‖v‖ ^ (2 : ℕ) = _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def]
  change Complex.reCLM (∫ q, inner ℂ (v q) (v q) ∂D.quotientMeasure) = _
  rw [← Complex.reCLM.integral_comp_comm hI]
  apply integral_congr_ae
  filter_upwards [he] with q hq
  change RCLike.re (inner ℂ (v q) (v q)) = _
  rw [hq, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact residualCoefficient_norm_sq k R hR q

end
end ManuscriptAudit.Paper9ResidualVector

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9ResidualVector.residualCoefficient_at_high,
      ``ManuscriptAudit.Paper9ResidualVector.residualCoefficient_norm_sq,
      ``ManuscriptAudit.Paper9ResidualVector.residualCoefficient_memLp,
      ``ManuscriptAudit.Paper9ResidualVector.residualVector_norm_sq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
