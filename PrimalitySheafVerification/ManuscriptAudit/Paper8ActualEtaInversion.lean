import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaInversionDerivative

/-!
# The actual Dedekind eta transformation under S

The principal square root of -iz is analytic on the upper half plane.
The eta inversion quotient has logarithmic derivative zero and value
one at i. This proves the generator transformation without assuming
the eta modular transformation law.
-/

namespace ManuscriptAudit.Paper8ActualEtaInversion

open UpperHalfPlane Set

noncomputable section

def inversionArgument (z : ℂ) : ℂ := -(z⁻¹)

def principalFactor (z : ℂ) : ℂ :=
  Complex.exp (Complex.log (-Complex.I * z) / 2)

theorem inversionArgument_eq (z : ℍ) :
    inversionArgument z = ((ModularGroup.S • z : ℍ) : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [inversionArgument, inv_neg]

private theorem inversionArgument_hasDerivAt {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt inversionArgument (z ^ 2)⁻¹ z := by
  have hFun : (-(fun w : ℂ => w⁻¹)) = inversionArgument := rfl
  rw [← hFun]
  simpa only [neg_neg] using (hasDerivAt_inv hz).neg

theorem principalFactor_ne_zero (z : ℂ) : principalFactor z ≠ 0 :=
  Complex.exp_ne_zero _

private theorem principalFactor_hasDerivAt (z : ℍ) :
    HasDerivAt principalFactor (principalFactor z * (1 / (2 * (z : ℂ)))) z := by
  have hRe : 0 < (-Complex.I * (z : ℂ)).re := by
    simpa [Complex.mul_re, Complex.mul_im] using z.im_pos
  have hSlit : -Complex.I * (z : ℂ) ∈ Complex.slitPlane := Or.inl hRe
  have hLin : HasDerivAt (fun w : ℂ => -Complex.I * w) (-Complex.I) z := by
    simpa only [id, mul_one] using (hasDerivAt_id (z : ℂ)).const_mul (-Complex.I)
  have hLog := (Complex.hasDerivAt_log hSlit).comp (z : ℂ) hLin
  have hHalf := hLog.div_const (2 : ℂ)
  have hCancel : (((-Complex.I * (z : ℂ))⁻¹) * -Complex.I) / 2 = 1 / (2 * (z : ℂ)) := by
    field_simp [Complex.I_ne_zero, z.ne_zero] <;> ring
  rw [hCancel] at hHalf
  exact (Complex.hasDerivAt_exp (Complex.log (-Complex.I * (z : ℂ)) / 2)).comp (z : ℂ) hHalf

theorem principalFactor_logDeriv (z : ℍ) :
    logDeriv principalFactor z = 1 / (2 * (z : ℂ)) := by
  rw [logDeriv_apply, (principalFactor_hasDerivAt z).deriv, mul_comm,
    mul_div_cancel_right₀ _ (principalFactor_ne_zero z)]

private theorem eta_composed_logDeriv (z : ℍ) :
    logDeriv (ModularForm.eta ∘ inversionArgument) z =
      logDeriv ModularForm.eta z + 1 / (2 * (z : ℂ)) := by
  have hS := inversionArgument_hasDerivAt z.ne_zero
  have hIm : inversionArgument z ∈ upperHalfPlaneSet := by
    rw [inversionArgument_eq]
    exact (ModularGroup.S • z).im_pos
  rw [logDeriv_comp (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hIm)
    hS.differentiableAt, hS.deriv, inversionArgument_eq]
  exact Paper8ActualEtaInversionDerivative.eta_logDeriv_inversion z

private def inversionRatio (z : ℂ) : ℂ :=
  (ModularForm.eta ∘ inversionArgument) z / (principalFactor z * ModularForm.eta z)

private theorem inversionRatio_local (z : ℍ) :
    DifferentiableAt ℂ inversionRatio z ∧ deriv inversionRatio z = 0 := by
  have hz := z.im_pos
  have hS := inversionArgument_hasDerivAt z.ne_zero
  have hIm : inversionArgument z ∈ upperHalfPlaneSet := by
    rw [inversionArgument_eq]
    exact (ModularGroup.S • z).im_pos
  have hEta := ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz
  have hF := (principalFactor_hasDerivAt z).differentiableAt
  have hD := hF.mul hEta
  have hDen : principalFactor z * ModularForm.eta z ≠ 0 :=
    mul_ne_zero (principalFactor_ne_zero z) (ModularForm.eta_ne_zero hz)
  have hEtaS := (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hIm).comp
    (z : ℂ) hS.differentiableAt
  have hEtaSNe : (ModularForm.eta ∘ inversionArgument) z ≠ 0 :=
    ModularForm.eta_ne_zero hIm
  refine ⟨hEtaS.div hD hDen, ?_⟩
  have hZero : logDeriv inversionRatio z = 0 := by
    unfold inversionRatio
    rw [logDeriv_div (z : ℂ) hEtaSNe hDen hEtaS hD,
      logDeriv_mul (z : ℂ) (principalFactor_ne_zero z) (ModularForm.eta_ne_zero hz) hF hEta,
      eta_composed_logDeriv z, principalFactor_logDeriv z]
    ring
  have hRatio : inversionRatio z ≠ 0 := div_ne_zero hEtaSNe hDen
  rw [logDeriv_apply] at hZero
  simpa only [zero_mul] using (div_eq_iff hRatio).mp hZero

private theorem inversionRatio_at_I : inversionRatio Complex.I = 1 := by
  have hEta : ModularForm.eta Complex.I ≠ 0 :=
    ModularForm.eta_ne_zero (by simp [upperHalfPlaneSet])
  unfold inversionRatio inversionArgument principalFactor
  simp [Complex.I_mul_I, neg_mul, hEta]

theorem eta_inversion (z : ℍ) :
    ModularForm.eta ((ModularGroup.S • z : ℍ) : ℂ) =
      principalFactor z * ModularForm.eta z := by
  have hConst : upperHalfPlaneSet.EqOn inversionRatio (fun _ : ℂ => (1 : ℂ)) := by
    refine isOpen_upperHalfPlaneSet.eqOn_of_deriv_eq
      (convex_halfSpace_im_gt 0).isPreconnected
      (fun w hw => (inversionRatio_local ⟨w, hw⟩).1.differentiableWithinAt)
      (differentiableOn_const (1 : ℂ)) ?_ (show Complex.I ∈ upperHalfPlaneSet by simp [upperHalfPlaneSet])
      inversionRatio_at_I
    intro w hw
    rw [(inversionRatio_local ⟨w, hw⟩).2, deriv_const]
  have hz := hConst z.im_pos
  have hDen : principalFactor z * ModularForm.eta z ≠ 0 :=
    mul_ne_zero (principalFactor_ne_zero z) (ModularForm.eta_ne_zero z.im_pos)
  have hProd := (div_eq_iff hDen).mp
    (show (ModularForm.eta ∘ inversionArgument) z /
      (principalFactor z * ModularForm.eta z) = 1 from hz)
  simpa only [Function.comp_apply, inversionArgument_eq, one_mul] using hProd

end
end ManuscriptAudit.Paper8ActualEtaInversion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaInversion.inversionArgument_eq,
      ``ManuscriptAudit.Paper8ActualEtaInversion.principalFactor_logDeriv,
      ``ManuscriptAudit.Paper8ActualEtaInversion.eta_inversion] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
