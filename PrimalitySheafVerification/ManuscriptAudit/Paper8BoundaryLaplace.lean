import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Order.Field

/-! A convergent bounded tail cannot produce a nonzero off-real boundary residue. -/

namespace ManuscriptAudit.Paper8BoundaryLaplace

open Set Filter MeasureTheory Complex
open scoped Topology

noncomputable section

def boundaryLaplace (B : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, B t * Complex.exp (-z * (t : ℂ))

private def vertical (ε τ : ℝ) : ℂ := (ε : ℂ) + (τ : ℂ) * Complex.I

private theorem vertical_re (ε τ : ℝ) : (vertical ε τ).re = ε := by
  simp [vertical, Complex.add_re, Complex.mul_re]

private theorem norm_vertical_exponential (ε τ t : ℝ) :
    ‖Complex.exp (-vertical ε τ * (t : ℂ))‖ = Real.exp (-ε * t) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, vertical_re]

private theorem weighted_integrable (B : ℝ → ℂ) (hB : Measurable B) {C : ℝ}
    (hBound : ∀ t > 0, ‖B t‖ ≤ C) {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    IntegrableOn (fun t : ℝ => B t * Complex.exp (-vertical ε τ * (t : ℂ))) (Ioi 0) := by
  have hInt := (integrableOn_exp_mul_Ioi (a := -ε) (neg_lt_zero.mpr hε) 0).const_mul C
  have hM : Measurable (fun t : ℝ => Complex.exp (-vertical ε τ * (t : ℂ))) := by fun_prop
  refine hInt.mono' (hB.mul hM).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, norm_vertical_exponential]
  exact mul_le_mul_of_nonneg_right (hBound x hx) (Real.exp_nonneg _)

theorem scaled_boundaryLaplace_tendsto_zero (B : ℝ → ℂ) (hB : Measurable B) {C : ℝ}
    (hBound : ∀ t > 0, ‖B t‖ ≤ C) (hTail : Tendsto B atTop (𝓝 0)) (τ : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * boundaryLaplace B (vertical ε τ)) (𝓝[>] 0) (𝓝 0) := by
  let G (ε t : ℝ) := B (ε⁻¹ * t) * Complex.exp (-vertical ε τ * ((ε⁻¹ * t : ℝ) : ℂ))
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hNorm (ε t : ℝ) (he : 0 < ε) : ‖G ε t‖ = ‖B (ε⁻¹ * t)‖ * Real.exp (-t) := by
    unfold G
    rw [norm_mul, norm_vertical_exponential, neg_mul, ← mul_assoc, mul_inv_cancel₀ he.ne', one_mul]
  have hMeas (ε : ℝ) : AEStronglyMeasurable (G ε) (volume.restrict (Ioi 0)) := by
    have hScale : Measurable (fun t : ℝ => ε⁻¹ * t) := measurable_const.mul measurable_id
    have hExp : Measurable (fun t : ℝ => Complex.exp (-vertical ε τ * ((ε⁻¹ * t : ℝ) : ℂ))) := by fun_prop
    exact ((hB.comp hScale).mul hExp).aestronglyMeasurable
  have hDom : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ t ∂volume.restrict (Ioi 0),
      ‖G ε t‖ ≤ C * Real.exp (-t) := by
    filter_upwards [hε] with ε he
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hNorm ε t he]
    exact mul_le_mul_of_nonneg_right (hBound _ (mul_pos (inv_pos.mpr he) ht)) (Real.exp_nonneg _)
  have hLim : ∀ᵐ t ∂volume.restrict (Ioi 0), Tendsto (fun ε => G ε t) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    have hScale : Tendsto (fun ε : ℝ => ε⁻¹ * t) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.atTop_mul_const ht'
    have hTailNorm : Tendsto (fun ε : ℝ => ‖B (ε⁻¹ * t)‖ * Real.exp (-t)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [norm_zero, zero_mul] using (hTail.comp hScale).norm.mul_const (Real.exp (-t))
    apply Metric.tendsto_nhds.2
    intro δ hδ
    filter_upwards [hε, (Metric.tendsto_nhds.1 hTailNorm) δ hδ] with ε he hδ'
    simpa only [dist_zero_right, hNorm ε t he, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg (-t)), abs_of_nonneg (norm_nonneg (B (ε⁻¹ * t)))] using hδ'
  have hI : Tendsto (fun ε : ℝ => ∫ t in Ioi 0, G ε t) (𝓝[>] 0) (𝓝 0) := by
    simpa only [integral_zero] using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun t : ℝ => C * Real.exp (-t))
        (Eventually.of_forall hMeas) hDom ((integrableOn_exp_neg_Ioi 0).const_mul C) hLim)
  apply hI.congr'
  filter_upwards [hε] with ε he
  have hScale := integral_comp_mul_left_Ioi
    (fun t : ℝ => B t * Complex.exp (-vertical ε τ * (t : ℂ))) 0 (inv_pos.mpr he)
  simpa only [G, boundaryLaplace, inv_inv, mul_zero, Complex.real_smul] using hScale

private theorem boundaryLaplace_const (L : ℂ) {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    boundaryLaplace (fun _ => L) (vertical ε τ) = L / vertical ε τ := by
  have hN : (-vertical ε τ).re < 0 := by rw [Complex.neg_re, vertical_re]; exact neg_lt_zero.mpr hε
  unfold boundaryLaplace
  rw [integral_const_mul, integral_exp_mul_complex_Ioi hN]
  simp [div_eq_mul_inv, Complex.ofReal_zero, mul_zero]

theorem off_real_scaled_boundaryLaplace_tendsto_zero (B : ℝ → ℂ) (hB : Measurable B) {C : ℝ}
    (hBound : ∀ t > 0, ‖B t‖ ≤ C) {L : ℂ} (hTail : Tendsto B atTop (𝓝 L))
    {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * boundaryLaplace B (vertical ε τ)) (𝓝[>] 0) (𝓝 0) := by
  let G (t : ℝ) := B t - L
  have hG : Measurable G := hB.sub measurable_const
  have hBoundG (t : ℝ) (ht : 0 < t) : ‖G t‖ ≤ C + ‖L‖ :=
    (norm_sub_le _ _).trans (add_le_add_right (hBound t ht) _)
  have hTailG : Tendsto G atTop (𝓝 0) := by simpa only [G, sub_self] using hTail.sub_const L
  have hLimit := scaled_boundaryLaplace_tendsto_zero G hG hBoundG hTailG τ
  have ht0 : vertical 0 τ ≠ 0 := by
    unfold vertical
    rw [Complex.ofReal_zero, zero_add]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hτ) Complex.I_ne_zero
  have hV : Continuous (fun ε : ℝ => vertical ε τ) := Complex.continuous_ofReal.add continuous_const
  have hCont : ContinuousAt (fun ε : ℝ => (ε : ℂ) * (L / vertical ε τ)) 0 :=
    Complex.continuous_ofReal.continuousAt.mul (continuousAt_const.div hV.continuousAt ht0)
  have hConst : Tendsto (fun ε : ℝ => (ε : ℂ) * (L / vertical ε τ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero, zero_mul] using hCont.tendsto.mono_left nhdsWithin_le_nhds
  have hBoth : Tendsto (fun ε : ℝ => (ε : ℂ) * boundaryLaplace G (vertical ε τ) +
      (ε : ℂ) * (L / vertical ε τ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_add] using hLimit.add hConst
  apply hBoth.congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε)] with ε he
  have hGInt := weighted_integrable G hG hBoundG he τ
  have hConstInt := weighted_integrable (fun _ => L) measurable_const (C := ‖L‖) (fun _ _ => le_rfl) he τ
  have hEq : boundaryLaplace B (vertical ε τ) =
      boundaryLaplace G (vertical ε τ) + L / vertical ε τ := by
    rw [← boundaryLaplace_const L he τ]
    unfold boundaryLaplace
    rw [← integral_add hGInt hConstInt]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by unfold G; ring)
  rw [hEq, mul_add]

end
end ManuscriptAudit.Paper8BoundaryLaplace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8BoundaryLaplace.off_real_scaled_boundaryLaplace_tendsto_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
