import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.Discriminant
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelZeroMode

/-!
# The actual Dedekind eta transformation under S

Mathlib's native S inversion is expressed using √z/√i. This adapter
identifies that factor with the exact exponential of the principal
logarithm of -iz.
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

theorem sqrt_I_eq_etaPhase :
    Complex.sqrt Complex.I = Paper8EtaLevelZeroMode.etaPhase := by
  unfold Complex.sqrt Paper8EtaLevelZeroMode.etaPhase Paper8HolomorphicPartPhase.periodCoefficient
  rw [Complex.cpow_def_of_ne_zero Complex.I_ne_zero, Complex.log_I]
  congr 1
  push_cast
  ring

theorem principalFactor_eq_native (z : ℍ) :
    principalFactor z = (Complex.sqrt Complex.I)⁻¹ * Complex.sqrt z := by
  have hArg0 : 0 ≤ (z : ℂ).arg := Complex.arg_nonneg_iff.mpr z.im_pos.le
  have hArgPi : (z : ℂ).arg ≤ Real.pi := Complex.arg_le_pi z
  have hArg : (-Complex.I).arg + (z : ℂ).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_neg_I]
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hLog : Complex.log (-Complex.I * (z : ℂ)) =
      Complex.log (-Complex.I) + Complex.log z :=
    (Complex.log_mul (neg_ne_zero.mpr Complex.I_ne_zero) z.ne_zero) hArg
  unfold principalFactor Complex.sqrt
  rw [Complex.cpow_def_of_ne_zero Complex.I_ne_zero, Complex.cpow_def_of_ne_zero z.ne_zero,
    ← Complex.exp_neg, ← Complex.exp_add, hLog, Complex.log_I, Complex.log_neg_I]
  congr 1
  ring

theorem eta_inversion (z : ℍ) :
    ModularForm.eta ((ModularGroup.S • z : ℍ) : ℂ) =
      principalFactor z * ModularForm.eta z := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv z.im_pos
  change ModularForm.eta (-1 / (z : ℂ)) =
    (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * ModularForm.eta z) at h
  rw [← inversionArgument_eq, principalFactor_eq_native, mul_assoc]
  simpa only [inversionArgument, neg_div, one_div] using h

end
end ManuscriptAudit.Paper8ActualEtaInversion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaInversion.inversionArgument_eq,
      ``ManuscriptAudit.Paper8ActualEtaInversion.principalFactor_logDeriv,
      ``ManuscriptAudit.Paper8ActualEtaInversion.sqrt_I_eq_etaPhase,
      ``ManuscriptAudit.Paper8ActualEtaInversion.principalFactor_eq_native,
      ``ManuscriptAudit.Paper8ActualEtaInversion.eta_inversion] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
