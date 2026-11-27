import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaNormCusp
import PrimalitySheafVerification.ManuscriptAudit.SubPoleCuspLimit

/-! A bounded weight-one-half translate divided by the actual eta product
has a finite limit at every periodic cusp of width below twenty-four. -/

namespace ManuscriptAudit.Paper8EtaRatioCuspLimit

open Set Filter Function UpperHalfPlane
open scoped MatrixGroups Manifold Topology
open Paper8ActualEtaSquaredModularity Paper8ActualEtaNormCusp

theorem eta_norm_transform (g : SL(2, ℤ)) (z : ℍ) :
    ‖ModularForm.eta (g • z : ℍ)‖ =
      Real.sqrt ‖denominator g z‖ * ‖ModularForm.eta z‖ := by
  have h := congrArg Real.sqrt (eta_norm_square_transform g z)
  simpa only [Real.sqrt_mul (norm_nonneg (denominator g z)) _, Real.sqrt_sq (norm_nonneg _)] using h

theorem eta_ratio_subPole_growth {f : ℍ → ℂ} (g : SL(2, ℤ)) {w : ℕ} (hw : 0 < w)
    {M : ℝ} (hM : 0 ≤ M)
    (hBound : ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z)‖ ≤ M * Real.sqrt ‖denominator g z‖) :
    ∀ᶠ z : ℍ in atImInfty,
      ‖f (g • z) / ModularForm.eta (g • z : ℍ)‖ ≤
        (2 * M) / ‖Periodic.qParam (w : ℝ) z‖ ^ ((w : ℝ) / 24) := by
  filter_upwards [hBound, eta_eventual_lower_bound hw] with z hF hLower
  have hD : 0 < Real.sqrt ‖denominator g z‖ :=
    Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))
  have hEta : 0 < ‖ModularForm.eta z‖ :=
    norm_pos_iff.mpr (ModularForm.eta_ne_zero z.im_pos)
  have hQ : 0 < ‖Periodic.qParam (w : ℝ) z‖ ^ ((w : ℝ) / 24) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _)) _
  rw [norm_div, eta_norm_transform]
  calc
    _ ≤ (M * Real.sqrt ‖denominator g z‖) /
          (Real.sqrt ‖denominator g z‖ * ‖ModularForm.eta z‖) :=
      div_le_div_of_nonneg_right hF (by positivity)
    _ = M / ‖ModularForm.eta z‖ := by
      field_simp [hD.ne', hEta.ne'] <;> ring
    _ ≤ _ := by
      rw [div_le_div_iff₀ hEta hQ]
      nlinarith [mul_le_mul_of_nonneg_left hLower hM]

theorem exists_limit_of_subPoleGrowth {F : ℍ → ℂ} {w C exponent : ℝ}
    (hw : 0 < w) (hPer : Periodic (F ∘ ofComplex) w) (hExp : exponent < 1)
    (hHol : MDiff F)
    (hBound : ∀ᶠ z : ℍ in atImInfty, ‖F z‖ ≤ C / ‖Periodic.qParam w z‖ ^ exponent) :
    ∃ L : ℂ, Tendsto F atImInfty (𝓝 L) := by
  have hPositive : ∀ᶠ z : ℂ in comap Complex.im atTop, 0 < z.im :=
    preimage_mem_comap (Ioi_mem_atTop 0)
  have hHolC : ∀ᶠ z : ℂ in comap Complex.im atTop, DifferentiableAt ℂ (F ∘ ofComplex) z :=
    hPositive.mono (fun z hz => UpperHalfPlane.mdifferentiableAt_iff.mp (hHol ⟨z, hz⟩))
  have hBoundC : ∀ᶠ z : ℂ in comap Complex.im atTop,
      ‖(F ∘ ofComplex) z‖ ≤ C / ‖Periodic.qParam w z‖ ^ exponent := by
    filter_upwards [tendsto_comap_im_ofComplex.eventually hBound, hPositive] with z hF hz
    simpa only [Function.comp_def, ofComplex_apply_of_im_pos hz] using hF
  obtain ⟨L, hL⟩ := SubPoleCuspLimit.exists_limit_of_subPole_cuspGrowth hw hPer hExp hHolC hBoundC
  refine ⟨L, ?_⟩
  simpa only [Function.comp_def, ofComplex_apply] using hL.comp tendsto_coe_atImInfty

theorem eta_ratio_limit {f : ℍ → ℂ} (g : SL(2, ℤ)) {w : ℕ}
    (hw : 0 < w) (hw24 : w < 24) {M : ℝ} (hM : 0 ≤ M)
    (hPer : Periodic ((fun z : ℍ => f (g • z) / ModularForm.eta (g • z : ℍ)) ∘ ofComplex) (w : ℝ))
    (hHol : MDiff (fun z : ℍ => f (g • z) / ModularForm.eta (g • z : ℍ)))
    (hBound : ∀ᶠ z : ℍ in atImInfty, ‖f (g • z)‖ ≤ M * Real.sqrt ‖denominator g z‖) :
    ∃ L : ℂ, Tendsto (fun z : ℍ => f (g • z) / ModularForm.eta (g • z : ℍ)) atImInfty (𝓝 L) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hwR24 : (w : ℝ) < 24 := by exact_mod_cast hw24
  exact exists_limit_of_subPoleGrowth hwR hPer (by linarith) hHol (eta_ratio_subPole_growth g hw hM hBound)

end ManuscriptAudit.Paper8EtaRatioCuspLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaRatioCuspLimit.eta_norm_transform,
      ``ManuscriptAudit.Paper8EtaRatioCuspLimit.eta_ratio_subPole_growth,
      ``ManuscriptAudit.Paper8EtaRatioCuspLimit.exists_limit_of_subPoleGrowth,
      ``ManuscriptAudit.Paper8EtaRatioCuspLimit.eta_ratio_limit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
