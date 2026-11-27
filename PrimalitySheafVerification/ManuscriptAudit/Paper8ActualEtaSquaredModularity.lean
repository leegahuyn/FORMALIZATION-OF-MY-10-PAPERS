import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaLogDerivative

/-!
# Native modularity up to a constant of the square of the eta product

The squared ratio avoids any square-root branch. For each integral
determinant-one matrix, the actual eta square transforms with the
weight-one denominator and a nonzero scalar independent of the point.
-/

namespace ManuscriptAudit.Paper8ActualEtaSquaredModularity

open Matrix UpperHalfPlane Set
open scoped MatrixGroups

noncomputable section

def denominator (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (g 1 0 : ℂ) * z + (g 1 1 : ℂ)

def fractionalLinear (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / denominator g z

theorem denominator_eq (g : SL(2, ℤ)) (z : ℍ) :
    denominator g z = UpperHalfPlane.denom (g : GL (Fin 2) ℝ) z :=
  (ModularGroup.denom_apply g z).symm

theorem denominator_ne_zero (g : SL(2, ℤ)) (z : ℍ) :
    denominator g z ≠ 0 := by
  rw [denominator_eq]
  exact UpperHalfPlane.denom_ne_zero _ _

theorem fractionalLinear_eq (g : SL(2, ℤ)) (z : ℍ) :
    fractionalLinear g z = ((g • z : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [fractionalLinear, denominator]

private theorem denominator_hasDerivAt (g : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (denominator g) (g 1 0 : ℂ) z := by
  simpa only [denominator, id, mul_one] using
    (((hasDerivAt_id z).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ))

private theorem fractionalLinear_hasDerivAt (g : SL(2, ℤ)) (z : ℍ) :
    HasDerivAt (fractionalLinear g) ((denominator g z) ^ 2)⁻¹ z := by
  have hN : HasDerivAt (fun w : ℂ => (g 0 0 : ℂ) * w + (g 0 1 : ℂ)) (g 0 0 : ℂ) z := by
    simpa only [id, mul_one] using
      (((hasDerivAt_id (z : ℂ)).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ))
  have hDet : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe g
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using
      congrArg (fun d : ℤ => (d : ℂ)) h
  have hNum : (g 0 0 : ℂ) * denominator g z -
      ((g 0 0 : ℂ) * (z : ℂ) + (g 0 1 : ℂ)) * (g 1 0 : ℂ) = 1 := by
    unfold denominator
    linear_combination hDet
  have h := hN.div (denominator_hasDerivAt g z) (denominator_ne_zero g z)
  rw [hNum, one_div] at h
  exact h

private def etaComposed (g : SL(2, ℤ)) : ℂ → ℂ :=
  ModularForm.eta ∘ fractionalLinear g

private theorem etaComposed_nonzero (g : SL(2, ℤ)) (z : ℍ) :
    etaComposed g z ≠ 0 := by
  unfold etaComposed
  rw [Function.comp_apply, fractionalLinear_eq]
  exact ModularForm.eta_ne_zero (g • z).im_pos

private theorem etaComposed_differentiableAt (g : SL(2, ℤ)) (z : ℍ) :
    DifferentiableAt ℂ (etaComposed g) z := by
  have hIm : fractionalLinear g z ∈ upperHalfPlaneSet := by
    rw [fractionalLinear_eq]
    exact (g • z).im_pos
  exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hIm).comp (z : ℂ)
    (fractionalLinear_hasDerivAt g z).differentiableAt

private theorem etaComposed_logDeriv (g : SL(2, ℤ)) (z : ℍ) :
    logDeriv (etaComposed g) z =
      logDeriv ModularForm.eta z + (g 1 0 : ℂ) / (2 * denominator g z) := by
  have hIm : fractionalLinear g z ∈ upperHalfPlaneSet := by
    rw [fractionalLinear_eq]
    exact (g • z).im_pos
  unfold etaComposed
  rw [logDeriv_comp (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hIm)
    (fractionalLinear_hasDerivAt g z).differentiableAt,
    (fractionalLinear_hasDerivAt g z).deriv, fractionalLinear_eq, denominator_eq]
  exact Paper8ActualEtaLogDerivative.eta_logDeriv_SL2 g z

private def squaredRatio (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (etaComposed g z * etaComposed g z) / (denominator g z * (ModularForm.eta z * ModularForm.eta z))

private theorem squaredRatio_nonzero (g : SL(2, ℤ)) (z : ℍ) :
    squaredRatio g z ≠ 0 := div_ne_zero
  (mul_ne_zero (etaComposed_nonzero g z) (etaComposed_nonzero g z))
  (mul_ne_zero (denominator_ne_zero g z)
    (mul_ne_zero (ModularForm.eta_ne_zero z.im_pos) (ModularForm.eta_ne_zero z.im_pos)))

private theorem squaredRatio_local (g : SL(2, ℤ)) (z : ℍ) :
    DifferentiableAt ℂ (squaredRatio g) z ∧ deriv (squaredRatio g) z = 0 := by
  have hE := ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos
  have hE0 := ModularForm.eta_ne_zero z.im_pos
  have hS := etaComposed_differentiableAt g z
  have hS0 := etaComposed_nonzero g z
  have hD := (denominator_hasDerivAt g z).differentiableAt
  have hD0 := denominator_ne_zero g z
  have hDen := mul_ne_zero hD0 (mul_ne_zero hE0 hE0)
  refine ⟨(hS.mul hS).div (hD.mul (hE.mul hE)) hDen, ?_⟩
  have hLog : logDeriv (squaredRatio g) z = 0 := by
    unfold squaredRatio
    rw [logDeriv_div z (mul_ne_zero hS0 hS0) hDen (hS.mul hS) (hD.mul (hE.mul hE)),
      logDeriv_mul z hS0 hS0 hS hS, logDeriv_mul z hD0 (mul_ne_zero hE0 hE0) hD (hE.mul hE),
      logDeriv_mul z hE0 hE0 hE hE, etaComposed_logDeriv]
    have hDLog : logDeriv (denominator g) z = (g 1 0 : ℂ) / denominator g z := by
      rw [logDeriv_apply, (denominator_hasDerivAt g z).deriv]
    rw [hDLog]
    field_simp [hD0] <;> ring
  rw [logDeriv_apply] at hLog
  simpa only [zero_mul] using (div_eq_iff (squaredRatio_nonzero g z)).mp hLog

def squaredMultiplier (g : SL(2, ℤ)) : ℂ :=
  squaredRatio g Complex.I

theorem squaredMultiplier_ne_zero (g : SL(2, ℤ)) :
    squaredMultiplier g ≠ 0 :=
  squaredRatio_nonzero g ⟨Complex.I, by simp⟩

theorem eta_squared_transform (g : SL(2, ℤ)) (z : ℍ) :
    ModularForm.eta ((g • z : ℍ) : ℂ) ^ 2 =
      squaredMultiplier g * (denominator g z * ModularForm.eta z ^ 2) := by
  have h : upperHalfPlaneSet.EqOn (squaredRatio g) (fun _ : ℂ => squaredMultiplier g) := by
    refine isOpen_upperHalfPlaneSet.eqOn_of_deriv_eq
      (Complex.convex_halfSpace_im_gt 0).isPreconnected
      (fun w hw => (squaredRatio_local g ⟨w, hw⟩).1.differentiableWithinAt)
      differentiableOn_const ?_ (show Complex.I ∈ upperHalfPlaneSet by simp [upperHalfPlaneSet]) rfl
    intro w hw
    rw [(squaredRatio_local g ⟨w, hw⟩).2, deriv_const]
  have hz := h z.im_pos
  have hDen := mul_ne_zero (denominator_ne_zero g z)
    (mul_ne_zero (ModularForm.eta_ne_zero z.im_pos) (ModularForm.eta_ne_zero z.im_pos))
  have hResult := (div_eq_iff hDen).mp (show
    (etaComposed g z * etaComposed g z) / (denominator g z * (ModularForm.eta z * ModularForm.eta z)) =
      squaredMultiplier g from hz)
  simpa only [etaComposed, Function.comp_apply, fractionalLinear_eq, pow_two] using hResult

end
end ManuscriptAudit.Paper8ActualEtaSquaredModularity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.denominator_eq,
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.fractionalLinear_eq,
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.squaredMultiplier_ne_zero,
      ``ManuscriptAudit.Paper8ActualEtaSquaredModularity.eta_squared_transform] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
