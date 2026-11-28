import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossAbelObstruction

/-! The extra factor of the shifted Dirichlet transform also rules out a residue at zero. -/

namespace ManuscriptAudit.Paper8OddCrossRealBoundary

open Filter Set MeasureTheory Paper8BoundaryLaplace Paper8OddCrossAbelObstruction
open scoped Topology

noncomputable section

theorem norm_real_scaled_boundaryLaplace_le (B : ℝ → ℂ) {C ε : ℝ}
    (hBound : ∀ t > 0, ‖B t‖ ≤ C) (hε : 0 < ε) :
    ‖(ε : ℂ) * boundaryLaplace B (ε : ℂ)‖ ≤ C := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f (t : ℝ) := B t * Complex.exp (-(ε : ℂ) * (t : ℂ))
  let g (t : ℝ) := C * Real.exp (-ε * t)
  have hInt : Integrable g μ :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0).const_mul C
  have hNorm : ∀ᵐ t ∂μ, ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    dsimp only [f, g]
    simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_right (hBound t ht) (Real.exp_nonneg _)
  have hDom : ‖boundaryLaplace B (ε : ℂ)‖ ≤ ∫ t, g t ∂μ :=
    (norm_integral_le_integral_norm f).trans
      (integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg (f t)) hInt hNorm)
  have hG : (∫ t, g t ∂μ) = C / ε := by
    change (∫ t : ℝ in Ioi 0, C * Real.exp (-ε * t)) = _
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hε)]
    simp [div_eq_mul_inv]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  calc
    _ ≤ ε * (∫ t, g t ∂μ) := mul_le_mul_of_nonneg_left hDom hε.le
    _ = C := by rw [hG]; field_simp [hε.ne']

theorem bounded_tail_forces_zero_at_real_abel_boundary (B : ℝ → ℂ) {C : ℝ}
    (hBound : ∀ t > 0, ‖B t‖ ≤ C) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ((ε : ℂ) * boundaryLaplace B (ε : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
  have hCont : Continuous (fun ε : ℝ => ε * C) := continuous_id.mul continuous_const
  have hC : Tendsto (fun ε : ℝ => ε * C) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using hCont.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply Metric.tendsto_nhds.2
  intro δ hδ
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε),
    (Metric.tendsto_nhds.1 hC) δ hδ] with ε hε hδ'
  have hb := norm_real_scaled_boundaryLaplace_le B hBound hε
  rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  apply (mul_le_mul_of_nonneg_left hb hε.le).trans_lt
  exact (le_abs_self (ε * C)).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hδ')

theorem ordered_cross_cutoff_forces_zero_at_every_abel_boundary {L : ℂ}
    (hL : Tendsto orderedCrossCutoff atTop (𝓝 L)) (τ : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * crossAbelShiftedZeta ((ε : ℂ) + (τ : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 0) := by
  by_cases hτ : τ = 0
  · subst τ
    obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1
      (Metric.isBounded_range_of_tendsto orderedCrossCutoff hL)
    have hB (t : ℝ) (_ : 0 < t) : ‖crossLogarithmicStep t‖ ≤ C := by
      have h := Metric.mem_ball.1 (hC (show crossLogarithmicStep t ∈ Set.range orderedCrossCutoff from ⟨_, rfl⟩))
      simpa only [dist_zero_right] using h.le
    have h := bounded_tail_forces_zero_at_real_abel_boundary crossLogarithmicStep hB
    have hCont : Continuous (fun ε : ℝ => (2 : ℂ) ^ (-((ε : ℂ) + 1))) := by
      simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.add continuous_const).neg)
    have hCont' := hCont.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero, zero_mul, add_zero, crossAbelShiftedZeta, mul_zero,
      mul_assoc, mul_left_comm, mul_comm] using hCont'.mul h
  · exact ordered_cross_cutoff_forces_zero_abel_residue hL hτ

end
end ManuscriptAudit.Paper8OddCrossRealBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossRealBoundary.norm_real_scaled_boundaryLaplace_le,
      ``ManuscriptAudit.Paper8OddCrossRealBoundary.ordered_cross_cutoff_forces_zero_at_every_abel_boundary] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
