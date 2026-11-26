import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import PrimalitySheafVerification.ManuscriptAudit.ThetaGammaTwoMetric

/-! Integrability of the actual theta density on the modular tile. -/

namespace ManuscriptAudit.ThetaHyperbolicTile

open Set MeasureTheory ModularGroup
open ThetaProfileGenerators ThetaGammaTwoMetric ThetaInfinityCusp
open Paper9ThetaCuspLTwo Paper9ThetaCuspPhases MaassLaplacian
open scoped UpperHalfPlane NNReal ENNReal

noncomputable section

private theorem fd_height (z : ℍ) (hz : z ∈ ModularGroup.fd) : (1 / 2 : ℝ) < z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  by_contra! hh
  nlinarith [mul_nonneg (sub_nonneg.mpr hh)
    (show (0 : ℝ) ≤ 1 / 2 + z.im by positivity)]

private theorem fd_in_rectangle :
    Complex.measurableEquivRealProd '' (UpperHalfPlane.coe '' ModularGroup.fd) ⊆
      Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (1 / 2) := by
  rintro _ ⟨c, ⟨z, hz, rfl⟩, rfl⟩
  change z.re ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ z.im ∈ Ioi (1 / 2)
  exact ⟨abs_le.mp hz.2, fd_height z hz⟩

private theorem integrable_majorant_fd (B : ℝ) :
    IntegrableOn (fun z : ℍ => B ^ 2 * z.im ^ (-(3 / 2 : ℝ))) ModularGroup.fd
      ((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
  let f : ℂ → ℝ := fun τ => B ^ 2 * τ.im ^ (-(3 / 2 : ℝ))
  let rect : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (1 / 2)
  have hPower := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (B ^ 2)
  have hr : IntegrableOn (fun z : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm z))
      rect volume := by
    change Integrable (fun z : ℝ × ℝ => B ^ 2 * z.2 ^ (-(3 / 2 : ℝ)))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict rect)
    dsimp only [rect]
    rw [← Measure.prod_restrict]
    exact hPower.comp_snd ((volume : Measure ℝ).restrict (Icc (-(1 / 2 : ℝ)) (1 / 2)))
  have hc := (Complex.volume_preserving_equiv_real_prod.integrableOn_image
      Complex.measurableEquivRealProd.measurableEmbedding
      (f := fun q => f (Complex.measurableEquivRealProd.symm q))
      (s := UpperHalfPlane.coe '' ModularGroup.fd)).mp (hr.mono_set fd_in_rectangle)
  have he := UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (f := f) (μ := (volume : Measure ℂ))
    (s := UpperHalfPlane.coe '' ModularGroup.fd)
    (Set.image_subset_range UpperHalfPlane.coe ModularGroup.fd)
  rw [Set.preimage_image_eq ModularGroup.fd UpperHalfPlane.coe_injective] at he
  exact he.mp (by simpa [Function.comp_def] using hc)

private def density (z : ℍ) : ℝ≥0∞ :=
  ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)

private theorem density_toReal (z : ℍ) : (density z).toReal = (z.im ^ 2)⁻¹ := by
  simp [density, one_div, inv_pow]

private theorem density_measurable : Measurable density := by
  have he : density = fun z => ENNReal.ofReal ((z.im ^ 2)⁻¹) := by
    funext z
    apply (ENNReal.toReal_eq_toReal_iff' (by simp [density]) ENNReal.ofReal_ne_top).mp
    rw [density_toReal, ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg _))]
  rw [he]
  exact (UpperHalfPlane.continuous_im.measurable.pow_const 2).inv.ennreal_ofReal

theorem bounded_profile_integrableOn_fd (F : ℂ → ℂ) (B : ℝ)
    (hF : Continuous fun z : ℍ => F (z : ℂ))
    (hB : ∀ z : ℍ, (1 / 2 : ℝ) ≤ z.im → ‖F (z : ℂ)‖ ≤ B) :
    IntegrableOn (thetaDensity F) ModularGroup.fd (volume : Measure ℍ) := by
  let μ := (volume : Measure ℂ).comap UpperHalfPlane.coe
  have hm : (volume : Measure ℍ) = μ.withDensity density := rfl
  have hD := density_measurable
  have hF' : Continuous (thetaDensity F) :=
    (Real.continuous_sqrt.comp UpperHalfPlane.continuous_im).mul (hF.norm.pow _)
  rw [hm, IntegrableOn, restrict_withDensity ModularGroup.isClosed_fd.measurableSet]
  apply (integrable_withDensity_iff_integrable_smul' hD (Filter.Eventually.of_forall
    (fun z : ℍ => by simp [density]))).2
  have hMeas : AEStronglyMeasurable (fun z : ℍ => (density z).toReal • thetaDensity F z)
      (μ.restrict ModularGroup.fd) := by
    simp only [smul_eq_mul]
    exact (hD.ennreal_toReal.mul hF'.measurable).aestronglyMeasurable
  apply Integrable.mono' (integrable_majorant_fd B) hMeas
  filter_upwards [self_mem_ae_restrict ModularGroup.isClosed_fd.measurableSet] with z hz
  rw [smul_eq_mul, density_toReal, Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)))]
  have he : (z.im ^ 2)⁻¹ * thetaDensity F z =
      ‖F (z : ℂ)‖ ^ 2 * z.im ^ (-(3 / 2 : ℝ)) := by
    rw [thetaDensity, Real.sqrt_eq_rpow, show -(3 / 2 : ℝ) = 1 / 2 - 2 by norm_num,
      Real.rpow_sub z.im_pos, Real.rpow_two, div_eq_mul_inv]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hB z (fd_height z hz).le) 2)
    (Real.rpow_nonneg z.im_pos.le _)

private theorem norm_standard_height {τ : ℂ} {H : ℝ}
    (hH : 0 < H) (hτ : H ≤ τ.im) : ‖jacobiTheta τ‖ ≤ thetaBound H := by
  have ht : complexPoint τ.re τ.im = τ := by apply Complex.ext <;> simp [complexPoint]
  rw [← ht]
  exact norm_theta_le hH hτ

private theorem shifted_profile_integrableOn_fd (t : ℝ) :
    IntegrableOn (thetaDensity (fun τ => jacobiTheta (τ + (t : ℂ)))) ModularGroup.fd volume := by
  apply bounded_profile_integrableOn_fd _ (thetaBound (1 / 2)) 
  · refine continuous_iff_continuousAt.mpr fun z => ?_
    have hC : Continuous (fun z : ℍ => (z : ℂ) + (t : ℂ)) :=
      UpperHalfPlane.continuous_coe.add continuous_const
    have him : (((z : ℂ) + (t : ℂ))).im = z.im := by simp
    exact ContinuousAt.comp' (f := fun z : ℍ => (z : ℂ) + (t : ℂ)) (x := z)
      (continuousAt_jacobiTheta (him.symm ▸ z.im_pos)) hC.continuousAt
  · intro z hz
    apply norm_standard_height (by norm_num : (0 : ℝ) < 1 / 2)
    simpa using hz

theorem profileDensity_integrableOn_fd (v : Direction) :
    IntegrableOn (profileDensity v) ModularGroup.fd (volume : Measure ℍ) := by
  rcases direction_cases v with rfl | rfl | rfl | rfl
  · change IntegrableOn (thetaDensity (profile (![0, 0] : Direction))) _ _
    rw [profile_00]
    have he : thetaDensity (0 : ℂ → ℂ) = 0 := by
      funext z
      simp [thetaDensity]
    rw [he]
    exact integrableOn_zero
  · change IntegrableOn (thetaDensity (profile (![1, 1] : Direction))) _ _
    rw [profile_11]
    simpa only [Complex.ofReal_zero, add_zero] using shifted_profile_integrableOn_fd 0
  · change IntegrableOn (thetaDensity (profile (![0, 1] : Direction))) _ _
    have he : thetaAlternating = fun τ => jacobiTheta (τ + (1 : ℂ)) :=
      funext fun τ => (jacobiTheta_add_one_profile τ).symm
    rw [profile_01, he]
    simpa only [Complex.ofReal_one] using shifted_profile_integrableOn_fd 1
  · change IntegrableOn (thetaDensity (profile (![1, 0] : Direction))) _ _
    rw [profile_10]
    apply bounded_profile_integrableOn_fd _ (halfBound (1 / 2))
    · refine continuous_iff_continuousAt.mpr fun z => ?_
      exact ContinuousAt.comp' (f := UpperHalfPlane.coe) (x := z)
        (continuousAt_thetaHalfShift z.im_pos) UpperHalfPlane.continuous_coe.continuousAt
    · intro z hz
      exact norm_thetaHalfShift_le (by norm_num) hz

end
end ManuscriptAudit.ThetaHyperbolicTile

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaHyperbolicTile.bounded_profile_integrableOn_fd,
      ``ManuscriptAudit.ThetaHyperbolicTile.profileDensity_integrableOn_fd] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
