import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import PrimalitySheafVerification.ManuscriptAudit.Paper8BoundaryLaplace

/-! A bounded measurable tail has a holomorphic Laplace transform on the right half-plane. -/

namespace ManuscriptAudit.Paper8BoundaryLaplaceHolomorphic

open Filter MeasureTheory Set Paper8BoundaryLaplace
open scoped Topology

noncomputable section

private theorem kernel_norm (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-z * (t : ℂ))‖ = Real.exp (-z.re * t) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

private theorem derivative_majorant {a C v t : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hv : 2 * a < v) (ht : 0 < t) :
    C * (Real.exp (-v * t) * t) ≤ (C / a) * Real.exp (-a * t) := by
  have h1 : t ≤ (1 / a) * Real.exp (a * t) := by
    have h := Real.add_one_le_exp (a * t)
    calc
      t = (1 / a) * (a * t) := by field_simp [ha.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : Real.exp (-v * t) ≤ Real.exp (-(2 * a) * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hv.le) ht.le)
  apply le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul h2 h1 ht.le (Real.exp_nonneg _)) hC)
  have he : Real.exp (-(2 * a) * t) * Real.exp (a * t) = Real.exp (-a * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (C / a) * (Real.exp (-(2 * a) * t) * Real.exp (a * t)) := by
      simp only [div_eq_mul_inv, one_mul]
      ring
    _ ≤ _ := by rw [he]

theorem differentiableOn_boundaryLaplace (B : ℝ → ℂ) (hB : Measurable B) {C : ℝ}
    (hBound : ∀ t > 0, ‖B t‖ ≤ C) :
    DifferentiableOn ℂ (boundaryLaplace B) {z : ℂ | 0 < z.re} := by
  intro z hz
  have hZ : 0 < z.re := hz
  have hC : 0 ≤ C := (norm_nonneg (B 1)).trans (hBound 1 zero_lt_one)
  let a := z.re / 4
  have ha : 0 < a := by unfold a; positivity
  let U : Set ℂ := {v | 2 * a < v.re}
  have hU : U ∈ 𝓝 z := by
    have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    apply hOpen.mem_nhds
    change 2 * (z.re / 4) < z.re
    linarith
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F (v : ℂ) (t : ℝ) := B t * Complex.exp (-v * (t : ℂ))
  let F' (v : ℂ) (t : ℝ) := B t * (Complex.exp (-v * (t : ℂ)) * -(t : ℂ))
  let M (t : ℝ) := (C / a) * Real.exp (-a * t)
  have hFm (v : ℂ) : AEStronglyMeasurable (F v) μ := by
    have h : Measurable (fun t : ℝ => Complex.exp (-v * (t : ℂ))) := by fun_prop
    exact (hB.mul h).aestronglyMeasurable
  have hFi : Integrable (F z) μ := by
    have hI : Integrable (fun t : ℝ => C * Real.exp (-z.re * t)) μ :=
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hZ) 0).const_mul C
    refine hI.mono' (hFm z) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖B t * Complex.exp (-z * (t : ℂ))‖ ≤ C * Real.exp (-z.re * t)
    rw [norm_mul, kernel_norm]
    exact mul_le_mul_of_nonneg_right (hBound t ht) (Real.exp_nonneg _)
  have hF'm : AEStronglyMeasurable (F' z) μ := by
    have h : Measurable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * -(t : ℂ)) := by fun_prop
    exact (hB.mul h).aestronglyMeasurable
  have hMi : Integrable M μ := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).const_mul (C / a)
  have hBnd : ∀ᵐ t ∂μ, ∀ v ∈ U, ‖F' v t‖ ≤ M t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro v hv
    have ht' : 0 < t := ht
    change 2 * a < v.re at hv
    unfold F' M
    rw [norm_mul, norm_mul, kernel_norm, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.le]
    exact (mul_le_mul_of_nonneg_right (hBound t ht') (by positivity)).trans
      (derivative_majorant ha hC hv ht')
  have hD : ∀ᵐ t ∂μ, ∀ v ∈ U, HasDerivAt (F · t) (F' v t) v := by
    refine Eventually.of_forall fun t v _ => ?_
    have hL := (hasDerivAt_id' v).neg.mul_const (t : ℂ)
    have hExp := (Complex.hasDerivAt_exp (-v * (t : ℂ))).comp v hL
    simpa only [F, F', Function.comp_def, Pi.neg_apply, id_eq, neg_one_mul] using hExp.const_mul (B t)
  have hDerivative := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hU (Eventually.of_forall hFm) hFi hF'm hBnd hMi hD).2
  exact hDerivative.differentiableAt.differentiableWithinAt

end
end ManuscriptAudit.Paper8BoundaryLaplaceHolomorphic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8BoundaryLaplaceHolomorphic.differentiableOn_boundaryLaplace
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
