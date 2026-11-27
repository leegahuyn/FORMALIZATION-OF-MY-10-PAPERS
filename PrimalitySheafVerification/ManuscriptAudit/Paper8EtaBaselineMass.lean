import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.OpenPos
import PrimalitySheafVerification.ManuscriptAudit.ModularDomainFiniteVolume
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPeterssonMass

/-! Positivity and finiteness of the actual eta Petersson mass. -/

namespace ManuscriptAudit.Paper8EtaBaselineMass

open Set Filter MeasureTheory UpperHalfPlane Function.Periodic
open Paper8EtaPeterssonMass Paper8ActualEtaNormCusp
open scoped ENNReal Topology NNReal

noncomputable section

private def realDensity (z : ℍ) : ℝ :=
  ‖ModularForm.eta z‖ ^ 2 * Real.sqrt z.im

private theorem continuous_realDensity : Continuous realDensity := by
  have hEta : Continuous (fun z : ℍ => ModularForm.eta (z : ℂ)) := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt
  exact (hEta.norm.pow 2).mul (Real.continuous_sqrt.comp UpperHalfPlane.continuous_im)

private theorem measurable_density : Measurable density :=
  continuous_realDensity.measurable.ennreal_ofReal

private theorem density_pos (z : ℍ) : 0 < density z := by
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (pow_pos (norm_pos_iff.mpr (ModularForm.eta_ne_zero z.im_pos)) 2)
    (Real.sqrt_pos.2 z.im_pos)

private theorem quadratic_q_tail :
    Tendsto (fun z : ℍ => ‖qParam 24 z‖ ^ 2 * Real.sqrt z.im) atImInfty (𝓝 0) := by
  have hIm : Tendsto UpperHalfPlane.im atImInfty atTop := by
    unfold atImInfty
    exact tendsto_comap
  have hDecay :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (Real.pi / 6) (by positivity)).comp hIm
  have hEq (z : ℍ) :
      ‖qParam 24 z‖ ^ 2 * Real.sqrt z.im =
        z.im ^ (1 / 2 : ℝ) * Real.exp (-(Real.pi / 6) * z.im) := by
    have hArg : -2 * Real.pi * z.im / 24 + (-2 * Real.pi * z.im / 24) =
        -(Real.pi / 6) * z.im := by ring
    rw [norm_qParam, UpperHalfPlane.coe_im, pow_two, ← Real.exp_add, hArg, Real.sqrt_eq_rpow]
    exact mul_comm _ _
  simpa only [Function.comp_apply, hEq] using hDecay

private theorem density_eventual_bound :
    ∀ᶠ z : ℍ in atImInfty, realDensity z ≤ 4 := by
  filter_upwards [eta_eventual_upper_bound, quadratic_q_tail.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with z hz hq
  have hs : ‖ModularForm.eta z‖ ^ 2 ≤ 4 * ‖qParam 24 z‖ ^ 2 := calc
    _ ≤ (2 * ‖qParam 24 z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    _ = _ := by ring
  change ‖qParam 24 z‖ ^ 2 * Real.sqrt z.im < 1 at hq
  calc
    realDensity z ≤ (4 * ‖qParam 24 z‖ ^ 2) * Real.sqrt z.im :=
      mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ = 4 * (‖qParam 24 z‖ ^ 2 * Real.sqrt z.im) := by ring
    _ ≤ 4 := by linarith only [hq]

private theorem density_bounded_on_fd :
    ∃ C : ℝ, ∀ z ∈ ModularGroup.fd, realDensity z ≤ C := by
  obtain ⟨Y, hY⟩ := (atImInfty_mem {z | realDensity z ≤ 4}).mp density_eventual_bound
  obtain ⟨C, hC⟩ := (ModularGroup.isCompact_truncatedFundamentalDomain Y).bddAbove_image
    continuous_realDensity.continuousOn
  refine ⟨max C 4, fun z hz => ?_⟩
  by_cases hIm : z.im ≤ Y
  · exact (hC (mem_image_of_mem realDensity ⟨hz, hIm⟩)).trans (le_max_left _ _)
  · have hz4 : realDensity z ≤ 4 := hY z (le_of_lt (lt_of_not_ge hIm))
    exact hz4.trans (le_max_right _ _)

theorem mass_fd_lt_top : mass ModularGroup.fd < ⊤ := by
  obtain ⟨C, hC⟩ := density_bounded_on_fd
  unfold mass
  refine (setLIntegral_mono (g := fun _ => ENNReal.ofReal C) measurable_const
    (fun z hz => ENNReal.ofReal_le_ofReal (hC z hz))).trans_lt ?_
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ModularDomainFiniteVolume.volume_fd_lt_top

theorem mass_fdo_lt_top : mass ModularGroup.fdo < ⊤ :=
  (lintegral_mono_set ModularGroup.fdo_subset_fd).trans_lt mass_fd_lt_top

private theorem volume_fdo_pos : 0 < (volume : Measure ℍ) ModularGroup.fdo := by
  let img := ((↑) : ℍ → ℂ) '' ModularGroup.fdo
  have hOpen : IsOpen img := isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo
  let z : ℍ := ⟨(⟨0, 2⟩ : ℂ), by norm_num⟩
  have hz : z ∈ ModularGroup.fdo := by
    change 1 < Complex.normSq (⟨0, 2⟩ : ℂ) ∧ |(0 : ℝ)| < 1 / 2
    norm_num [Complex.normSq_apply]
  have hImg : 0 < (volume : Measure ℂ) img :=
    hOpen.measure_pos volume ⟨(z : ℂ), mem_image_of_mem _ hz⟩
  let f : ℂ → ℝ≥0∞ := fun w => (↑((1 / ‖w.im‖₊ : ℝ≥0) ^ 2) : ℝ≥0∞)
  have hM : Measurable f := by
    unfold f
    fun_prop
  have hSupp : Function.support f ∩ img = img := by
    refine inter_eq_right.mpr ?_
    rintro _ ⟨w, _, rfl⟩
    have hw : ‖(w : ℂ).im‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr w.im_pos.ne'
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (div_ne_zero one_ne_zero hw))
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply (setLIntegral_pos_iff hM).mpr
  rwa [hSupp]

theorem mass_fdo_pos : 0 < mass ModularGroup.fdo := by
  have hSupp : Function.support density ∩ ModularGroup.fdo = ModularGroup.fdo :=
    inter_eq_right.mpr fun z _ => (density_pos z).ne'
  apply (setLIntegral_pos_iff measurable_density).mpr
  rwa [hSupp]

def baseline : ℝ := (mass ModularGroup.fdo).toReal

theorem baseline_pos : 0 < baseline :=
  ENNReal.toReal_pos mass_fdo_pos.ne' mass_fdo_lt_top.ne

end
end ManuscriptAudit.Paper8EtaBaselineMass

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaBaselineMass.mass_fd_lt_top,
      ``ManuscriptAudit.Paper8EtaBaselineMass.mass_fdo_lt_top,
      ``ManuscriptAudit.Paper8EtaBaselineMass.mass_fdo_pos,
      ``ManuscriptAudit.Paper8EtaBaselineMass.baseline_pos] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
