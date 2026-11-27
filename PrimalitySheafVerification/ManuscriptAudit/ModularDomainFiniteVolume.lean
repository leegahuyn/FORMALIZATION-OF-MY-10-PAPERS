import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-! The actual closed modular fundamental region has finite hyperbolic volume. -/

namespace ManuscriptAudit.ModularDomainFiniteVolume

open Set Filter MeasureTheory UpperHalfPlane
open scoped ENNReal Topology NNReal

private theorem reciprocal_square_integrable :
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ici (1 / 2 : ℝ)) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun y : ℝ => -y⁻¹) (l := 0) ?_ ?_ ?_
  · intro y hy
    have hy0 : 0 < y := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hy
    simpa only [neg_neg] using (hasDerivAt_inv hy0.ne').neg
  · exact fun y _ => inv_nonneg.mpr (sq_nonneg y)
  · simpa only [neg_zero] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).neg

private theorem reciprocal_square_lintegral_lt_top :
    (∫⁻ y : ℝ in Ici (1 / 2 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹)) < ⊤ :=
  (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall (fun y : ℝ => inv_nonneg.mpr (sq_nonneg y)))).mp
    reciprocal_square_integrable.hasFiniteIntegral

private def strip : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ici (1 / 2)

private def heightDensity (z : ℂ) : ℝ≥0∞ := ↑((1 / ‖z.im‖₊ : ℝ≥0) ^ 2)

private theorem height_density_on_strip {p : ℝ × ℝ} (hp : p ∈ strip) :
    heightDensity (Complex.measurableEquivRealProd.symm p) = ENNReal.ofReal ((p.2 ^ 2)⁻¹) := by
  have hp0 : 0 < p.2 := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hp.2
  rw [heightDensity, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [Complex.measurableEquivRealProd_symm_apply, Real.norm_eq_abs, abs_of_pos hp0, inv_pow]

private theorem strip_density_lintegral_lt_top :
    (∫⁻ p : ℝ × ℝ in strip, ENNReal.ofReal ((p.2 ^ 2)⁻¹)) < ⊤ := by
  unfold strip
  change (∫⁻ p in Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ici (1 / 2 : ℝ),
    ENNReal.ofReal ((p.2 ^ 2)⁻¹) ∂((volume : Measure ℝ).prod volume)) < ⊤
  rw [← Measure.prod_restrict]
  have hM : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((p.2 ^ 2)⁻¹)) := by fun_prop
  rw [lintegral_prod _ hM.aemeasurable, setLIntegral_const]
  exact ENNReal.mul_lt_top reciprocal_square_lintegral_lt_top isCompact_Icc.measure_lt_top

theorem volume_fd_lt_top : (volume : Measure ℍ) ModularGroup.fd < ⊤ := by
  let S := ((↑) : ℍ → ℂ) '' ModularGroup.fd
  let e := Complex.measurableEquivRealProd.symm
  have hPull : e ⁻¹' S ⊆ strip := by
    intro p hp
    obtain ⟨z, hz, he⟩ := hp
    have hRe : z.re = p.1 := by
      simpa only [UpperHalfPlane.coe_re, e, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.re he
    have hIm : z.im = p.2 := by
      simpa only [UpperHalfPlane.coe_im, e, Complex.measurableEquivRealProd_symm_apply] using
        congrArg Complex.im he
    have hLow : (1 / 2 : ℝ) ≤ z.im := by
      nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz, z.im_pos]
    have hReBound : |z.re| ≤ (1 / 2 : ℝ) := hz.2
    exact ⟨hRe ▸ abs_le.mp hReBound, hIm ▸ hLow⟩
  have hEq :
      (∫⁻ p in e ⁻¹' S, heightDensity (e p)) = ∫⁻ z in S, heightDensity z :=
    Complex.volume_preserving_equiv_real_prod.symm.setLIntegral_comp_preimage_emb
      e.measurableEmbedding heightDensity S
  have hVal : (volume : Measure ℍ) ModularGroup.fd = ∫⁻ z in S, heightDensity z :=
    UpperHalfPlane.volume_eq_lintegral _
  rw [hVal, ← hEq]
  refine (lintegral_mono_set hPull).trans_lt ?_
  rw [setLIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Ici)
    (fun p hp => height_density_on_strip hp)]
  exact strip_density_lintegral_lt_top

end ManuscriptAudit.ModularDomainFiniteVolume

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.ModularDomainFiniteVolume.volume_fd_lt_top
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
