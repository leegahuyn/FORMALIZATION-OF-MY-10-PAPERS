import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Modular
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaSquaredModularity

/-! Actual invariant modular height and smooth truncations for the Maass energy argument. -/

namespace ManuscriptAudit.Paper8ModularHeightCutoff

open Set Filter Function UpperHalfPlane
open Paper8ActualEtaSquaredModularity
open scoped MatrixGroups Manifold Topology

noncomputable section

def maximumHeight (z : ℍ) : ℝ :=
  (Classical.choose (ModularGroup.exists_max_im z) • z).im

theorem im_smul_le_maximumHeight (z : ℍ) (g : SL(2, ℤ)) :
    (g • z).im ≤ maximumHeight z :=
  Classical.choose_spec (ModularGroup.exists_max_im z) g

theorem maximumHeight_invariant (g : SL(2, ℤ)) (z : ℍ) :
    maximumHeight (g • z) = maximumHeight z := by
  apply le_antisymm
  · let a := Classical.choose (ModularGroup.exists_max_im (g • z : ℍ))
    change (a • (g • z)).im ≤ maximumHeight z
    rw [← mul_smul]
    exact im_smul_le_maximumHeight z (a * g)
  · let b := Classical.choose (ModularGroup.exists_max_im z)
    change (b • z).im ≤ maximumHeight (g • z)
    simpa only [mul_smul, inv_smul_smul] using im_smul_le_maximumHeight (g • z) (b * g⁻¹)

private theorem im_smul_le_inv_of_lowerLeft_nonzero (g : SL(2, ℤ)) (z : ℍ)
    (hc : g 1 0 ≠ 0) : (g • z).im ≤ 1 / z.im := by
  have hcSq : (1 : ℤ) ≤ (g 1 0) ^ 2 := by
    have hp : (0 : ℤ) < (g 1 0) ^ 2 := sq_pos_of_ne_zero hc
    omega
  have hcSqR : (1 : ℝ) ≤ ((g 1 0 : ℝ) ^ 2) := by exact_mod_cast hcSq
  have hIm : (denominator g z).im = (g 1 0 : ℝ) * z.im := by
    simp [denominator, Complex.mul_im]
  have hD : z.im ^ 2 ≤ Complex.normSq (denominator g z) := by
    rw [Complex.normSq_apply, hIm]
    nlinarith [sq_nonneg (denominator g z).re, mul_le_mul_of_nonneg_right hcSqR (sq_nonneg z.im)]
  rw [ModularGroup.im_smul_eq_div_normSq, ← denominator_eq]
  apply (div_le_iff₀ (Complex.normSq_pos.mpr (denominator_ne_zero g z))).2
  calc
    z.im = (1 / z.im) * z.im ^ 2 := by field_simp [z.im_pos.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)

theorem maximumHeight_le_max (z : ℍ) :
    maximumHeight z ≤ max z.im (1 / z.im) := by
  let g := Classical.choose (ModularGroup.exists_max_im z)
  change (g • z).im ≤ max z.im (1 / z.im)
  by_cases hc : g 1 0 = 0
  · obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc
    rw [hn z, ModularGroup.im_T_zpow_smul]
    exact le_max_left _ _
  · exact (im_smul_le_inv_of_lowerLeft_nonzero g z hc).trans (le_max_right _ _)

theorem maximumHeight_eq_im_of_gt_one (z : ℍ) (hz : 1 < z.im) : maximumHeight z = z.im := by
  have hInv : 1 / z.im ≤ z.im := (div_le_iff₀ z.im_pos).2 (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.le) (by positivity : 0 ≤ z.im + 1)])
  have h := maximumHeight_le_max z
  rw [max_eq_left hInv] at h
  exact le_antisymm h (by simpa only [one_smul] using im_smul_le_maximumHeight z 1)

theorem cutoff_eventually_eq_chart (φ : ℝ → ℝ) {Y : ℝ} (hY : 2 < Y)
    (hφ : ∀ t ≤ Y, φ t = 1) (z : ℍ) :
    ∃ g : SL(2, ℤ), (fun w : ℍ => φ (maximumHeight w)) =ᶠ[𝓝 z]
      (fun w : ℍ => φ ((g • w).im)) := by
  let g := Classical.choose (ModularGroup.exists_max_im z)
  have hg : (g • z).im = maximumHeight z := rfl
  have hAction : Continuous (fun w : ℍ => g • w) := by
    simpa only [ModularGroup.sl_moeb] using
      (continuous_const_smul (g : GL (Fin 2) ℝ))
  have hIm : Continuous (fun w : ℍ => (g • w).im) := UpperHalfPlane.continuous_im.comp hAction
  refine ⟨g, ?_⟩
  by_cases hz : 1 < maximumHeight z
  · filter_upwards [hIm.continuousAt.tendsto.eventually (Ioi_mem_nhds (hg.symm ▸ hz))] with w hw
    rw [← maximumHeight_invariant g w, maximumHeight_eq_im_of_gt_one (g • w) hw]
  · have hY0 : 0 < Y := by linarith
    have hHalf : (1 / 2 : ℝ) ≤ maximumHeight z := by
      obtain ⟨γ, hγ⟩ := ModularGroup.exists_one_half_le_im_smul z
      exact hγ.trans (im_smul_le_maximumHeight z γ)
    have hLo : 1 / Y < (g • z).im := by
      rw [hg]
      exact ((div_lt_iff₀ hY0).2 (by linarith : (1 : ℝ) < (1 / 2 : ℝ) * Y)).trans_le hHalf
    have hHi : (g • z).im < Y := by rw [hg]; linarith [not_lt.mp hz]
    filter_upwards [hIm.continuousAt.tendsto.eventually (Ioo_mem_nhds hLo hHi)] with w hw
    have hInv : 1 / (g • w : ℍ).im < Y := by
      apply (div_lt_iff₀ (g • w : ℍ).im_pos).2
      simpa only [mul_comm] using (div_lt_iff₀ hY0).mp hw.1
    have hLt : maximumHeight w < Y := by
      rw [← maximumHeight_invariant g w]
      exact (maximumHeight_le_max (g • w)).trans_lt (max_lt_iff.2 ⟨hw.2, hInv⟩)
    rw [hφ _ hLt.le, hφ _ hw.2.le]

theorem cutoff_real_smooth (φ : ℝ → ℝ) {n : ℕ∞ω} (hφSmooth : ContDiff ℝ n φ)
    {Y : ℝ} (hY : 2 < Y) (hφ : ∀ t ≤ Y, φ t = 1) :
    ContDiffOn ℝ n (fun w : ℂ => φ (maximumHeight (ofComplex w))) {w : ℂ | 0 < w.im} := by
  intro w hw
  let z : ℍ := ⟨w, hw⟩
  obtain ⟨g, hLocal⟩ := cutoff_eventually_eq_chart φ hY hφ z
  have hNum : ContDiffAt ℝ n (fun v : ℂ => (g 0 0 : ℂ) * v + (g 0 1 : ℂ)) w := by fun_prop
  have hDen : ContDiffAt ℝ n (denominator g) w := by unfold denominator; fun_prop
  have hFrac : ContDiffAt ℝ n (fractionalLinear g) w :=
    hNum.div hDen (denominator_ne_zero g z)
  have hIm : ContDiffAt ℝ n (fun v : ℂ => v.im) (fractionalLinear g w) :=
    Complex.imCLM.contDiff.contDiffAt
  have hSmooth : ContDiffAt ℝ n (fun v : ℂ => φ (fractionalLinear g v).im) w :=
    hφSmooth.contDiffAt.comp w (hIm.comp w hFrac)
  have hOf : Tendsto (fun v : ℂ => ofComplex v) (𝓝 w) (𝓝 z) := by
    have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 1) hw).continuousAt.tendsto
    simpa only [ofComplex_apply_of_im_pos hw, z] using hc
  apply ContDiffAt.contDiffWithinAt
  apply hSmooth.congr_of_eventuallyEq
  filter_upwards [hOf.eventually hLocal,
    Complex.continuous_im.continuousAt.tendsto.eventually (Ioi_mem_nhds hw)] with v hv hPos
  change φ (maximumHeight (ofComplex v)) = φ (fractionalLinear g v).im
  change φ (maximumHeight (ofComplex v)) = φ ((g • ofComplex v : ℍ).im) at hv
  have he := fractionalLinear_eq g (ofComplex v)
  rw [ofComplex_apply_of_im_pos hPos] at he
  change fractionalLinear g v = ((g • (⟨v, hPos⟩ : ℍ) : ℍ) : ℂ) at he
  rw [he]
  simpa only [ofComplex_apply_of_im_pos hPos, UpperHalfPlane.coe_im] using hv

theorem cutoff_nonzero_reduced_to_truncation (φ : ℝ → ℝ) {B : ℝ}
    (hφ : ∀ t, B < t → φ t = 0) {z : ℍ} (hz : φ (maximumHeight z) ≠ 0) :
    ∃ g : SL(2, ℤ), g • z ∈ ModularGroup.truncatedFundamentalDomain B := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hB : maximumHeight z ≤ B := le_of_not_gt (fun h => hz (hφ _ h))
  exact ⟨g, hg, (im_smul_le_maximumHeight z g).trans hB⟩

end
end ManuscriptAudit.Paper8ModularHeightCutoff

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ModularHeightCutoff.maximumHeight_invariant,
      ``ManuscriptAudit.Paper8ModularHeightCutoff.maximumHeight_le_max,
      ``ManuscriptAudit.Paper8ModularHeightCutoff.maximumHeight_eq_im_of_gt_one,
      ``ManuscriptAudit.Paper8ModularHeightCutoff.cutoff_eventually_eq_chart,
      ``ManuscriptAudit.Paper8ModularHeightCutoff.cutoff_real_smooth,
      ``ManuscriptAudit.Paper8ModularHeightCutoff.cutoff_nonzero_reduced_to_truncation] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
