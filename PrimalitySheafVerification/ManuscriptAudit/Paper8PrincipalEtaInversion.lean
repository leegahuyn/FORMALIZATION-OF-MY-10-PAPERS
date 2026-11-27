import Lean.Util.CollectAxioms
import Mathlib.Analysis.RCLike.Sqrt
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaInversion
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaTranslation
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaHalfWeightPhase

/-! Principal-square-root inversion and the two actual normalized eta generator phases. -/

namespace ManuscriptAudit.Paper8PrincipalEtaInversion

open UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8EtaHalfWeightPhase
open scoped MatrixGroups

theorem eta_S_transform (z : ℍ) :
    ModularForm.eta (ModularGroup.S • z : ℍ) =
      Complex.sqrt (-Complex.I * (z : ℂ)) * ModularForm.eta z := by
  rw [Complex.sqrt_eq_exp (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) z.ne_zero)]
  exact Paper8ActualEtaInversion.eta_inversion z

theorem positivePhase_S (z : ℍ) :
    positivePhase ModularGroup.S z = Complex.sqrt (-Complex.I * (z : ℂ)) /
      (Real.sqrt ‖(z : ℂ)‖ : ℂ) := by
  unfold positivePhase
  rw [eta_S_transform, denominator_eq, ModularGroup.denom_S]
  have h : 0 < Real.sqrt ‖(z : ℂ)‖ := Real.sqrt_pos.2 (norm_pos_iff.mpr z.ne_zero)
  field_simp [ModularForm.eta_ne_zero z.im_pos, Complex.ofReal_ne_zero.mpr h.ne'] <;> ring

theorem positivePhase_T (z : ℍ) :
    positivePhase ModularGroup.T z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 24) := by
  have hT : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, ModularGroup.coe_T]
    simp
  have hD : denominator ModularGroup.T z = 1 := by
    simp [denominator, ModularGroup.coe_T]
  have hEta : ModularForm.eta ((z : ℂ) + 1) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 24) * ModularForm.eta z := by
    simpa only [Int.cast_one, mul_one] using Paper8ActualEtaTranslation.eta_add_integer z 1
  unfold positivePhase
  rw [hT, hD, norm_one, Real.sqrt_one, Complex.ofReal_one, mul_one, hEta,
    mul_div_cancel_right₀ _ (ModularForm.eta_ne_zero z.im_pos)]

end ManuscriptAudit.Paper8PrincipalEtaInversion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8PrincipalEtaInversion.eta_S_transform,
      ``ManuscriptAudit.Paper8PrincipalEtaInversion.positivePhase_S,
      ``ManuscriptAudit.Paper8PrincipalEtaInversion.positivePhase_T] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
