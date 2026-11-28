import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.FDeriv.Congr
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCutoffTaper
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassWirtinger

/-! The global modular taper has a uniform hyperbolic derivative bound supported in the cusp tail. -/

namespace ManuscriptAudit.Paper8MaassCutoffDerivative

open Filter Function Set UpperHalfPlane MaassLaplacian
open Paper8MaassCutoffTaper Paper8ModularHeightCutoff Paper8MaassWirtinger
open Paper8ActualEtaSquaredModularity
open scoped MatrixGroups Topology

noncomputable section

def complexCutoff (Y : ℝ) (w : ℂ) : ℂ := (modularCutoff Y (ofComplex w) : ℂ)

private theorem derivativeZ_realHeight {a : ℝ → ℝ} {w : ℂ}
    (ha : DifferentiableAt ℝ a w.im) :
    derivativeZ (fun v : ℂ => (a v.im : ℂ)) w =
      -Complex.I * ((deriv a w.im : ℝ) : ℂ) / 2 := by
  let x := w.re
  let y := w.im
  have hPoint : complexPoint x y = w := Complex.re_add_im w
  let A (v : ℂ) : ℂ := (a v.im : ℂ)
  have hReal : DifferentiableAt ℝ A w :=
    ha.hasDerivAt.ofReal_comp.differentiableAt.comp w Complex.imCLM.differentiableAt
  have h := derivativeZ_eq_partials (F := A) (x := x) (y := y)
    (by rwa [hPoint])
  have hx : partialX (fun u v => A (complexPoint u v)) x y = 0 := by
    simp only [partialX, A, complexPoint_im, deriv_const]
  have hy : partialY (fun u v => A (complexPoint u v)) x y = ((deriv a y : ℝ) : ℂ) := by
    simpa only [partialY, A, complexPoint_im] using ha.hasDerivAt.ofReal_comp.deriv
  rw [hPoint, hx, hy, zero_sub] at h
  simpa only [A, y, neg_mul] using h

theorem derivativeZ_cutoff_chart {Y : ℝ} (hY : 2 < Y) (z : ℍ) :
    ∃ g : SL(2, ℤ), derivativeZ (complexCutoff Y) z =
      (denominator g z ^ 2)⁻¹ *
        (-Complex.I * ((deriv (taper Y) (g • z : ℍ).im : ℝ) : ℂ) / 2) := by
  let A (w : ℂ) := (taper Y w.im : ℂ)
  have hY0 : 0 < Y := by linarith
  obtain ⟨g, hChart⟩ := cutoff_eventually_eq_chart (taper Y) hY
    (fun _ h => taper_eq_one hY0 h) z
  have hTo : Tendsto (fun v : ℂ => ofComplex v) (𝓝 (z : ℂ)) (𝓝 z) := by
    simpa only [ofComplex_apply] using
      ((UpperHalfPlane.contMDiffAt_ofComplex (n := 1) z.im_pos).continuousAt.tendsto)
  have hLocal : complexCutoff Y =ᶠ[𝓝 (z : ℂ)] A ∘ fractionalLinear g := by
    filter_upwards [hTo.eventually hChart,
      Complex.continuous_im.continuousAt.tendsto.eventually (Ioi_mem_nhds z.im_pos)] with v hv hPos
    have hFrac := fractionalLinear_eq g (ofComplex v)
    rw [ofComplex_apply_of_im_pos hPos] at hFrac
    change fractionalLinear g v = ((g • (⟨v, hPos⟩ : ℍ) : ℍ) : ℂ) at hFrac
    change (taper Y (maximumHeight (ofComplex v)) : ℂ) =
      (taper Y (fractionalLinear g v).im : ℂ)
    rw [hFrac]
    have hEq : taper Y (maximumHeight (ofComplex v)) = taper Y (g • (⟨v, hPos⟩ : ℍ) : ℍ).im := by
      simpa only [ofComplex_apply_of_im_pos hPos] using hv
    exact congrArg Complex.ofReal hEq
  have hEq : derivativeZ (complexCutoff Y) z = derivativeZ (A ∘ fractionalLinear g) z := by
    unfold derivativeZ
    rw [hLocal.fderiv_eq (𝕜 := ℝ)]
  have hφ : Differentiable ℝ (taper Y) := (taper_smooth Y).differentiable (by simp)
  have hD : DifferentiableAt ℝ A (fractionalLinear g z) :=
    (hφ _).hasDerivAt.ofReal_comp.differentiableAt.comp _ Complex.imCLM.differentiableAt
  refine ⟨g, ?_⟩
  rw [hEq, derivativeZ_comp_holomorphic hD (fractionalLinear_hasDerivAt g z).differentiableAt,
    (fractionalLinear_hasDerivAt g z).deriv, fractionalLinear_eq]
  congr 1
  exact derivativeZ_realHeight (hφ _)

theorem complexCutoff_derivativeZ_zero_below {Y : ℝ} (hY : 2 < Y) (z : ℍ)
    (hz : maximumHeight z < Y) : derivativeZ (complexCutoff Y) z = 0 := by
  obtain ⟨g, h⟩ := derivativeZ_cutoff_chart hY z
  rw [h, taper_deriv_zero_below (by linarith)
    ((im_smul_le_maximumHeight z g).trans_lt hz), Complex.ofReal_zero, mul_zero, zero_div, mul_zero]

theorem complexCutoff_derivativeZ_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y > 2, ∀ z : ℍ,
      2 * z.im * ‖derivativeZ (complexCutoff Y) z‖ ≤ C := by
  obtain ⟨C, hC, hTaper⟩ := height_deriv_taper_uniform
  refine ⟨C, hC, fun Y hY z => ?_⟩
  obtain ⟨g, hg⟩ := derivativeZ_cutoff_chart hY z
  let r := ‖denominator g z‖
  let u := (g • z : ℍ).im
  let p := deriv (taper Y) u
  have hr : 0 < r := norm_pos_iff.mpr (denominator_ne_zero g z)
  have hu : 0 < u := (g • z : ℍ).im_pos
  have hIm : u = z.im / r ^ 2 := by
    unfold u r
    rw [ModularGroup.im_smul_eq_div_normSq, ← denominator_eq, Complex.normSq_eq_norm_sq]
  have hNorm : ‖derivativeZ (complexCutoff Y) z‖ = (r ^ 2)⁻¹ * (|p| / 2) := by
    rw [hg]
    change ‖(denominator g z ^ 2)⁻¹ * (-Complex.I * (p : ℂ) / 2)‖ = _
    have hTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    simp only [norm_mul, norm_div, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      norm_neg, Complex.norm_I, one_mul, hTwo, r]
  calc
    _ = |u * p| := by
      rw [hNorm, abs_mul, abs_of_pos hu, hIm]
      field_simp [hr.ne'] <;> ring
    _ ≤ C := hTaper Y (by linarith) u

end
end ManuscriptAudit.Paper8MaassCutoffDerivative

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassCutoffDerivative.complexCutoff_derivativeZ_uniform
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
