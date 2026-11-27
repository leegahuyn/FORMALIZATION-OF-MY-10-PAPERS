import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaSquaredModularity
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaTranslation

/-!
# Integral-weight modularity of the twenty-fourth power of the actual eta product

The existing native discriminant supplies the weight-twelve law.
The additional results compute the multiplicative scalar of the square
and its values at the two integral modular generators.
-/

namespace ManuscriptAudit.Paper8ActualEtaPowerModularity

open Matrix UpperHalfPlane Paper8ActualEtaSquaredModularity
open scoped MatrixGroups

noncomputable section

private def basePoint : ℍ := ⟨Complex.I, by simp⟩

private theorem denominator_mul (g h : SL(2, ℤ)) (z : ℍ) :
    denominator (g * h) z = denominator g (h • z : ℍ) * denominator h z := by
  have hNe := denominator_ne_zero h z
  rw [← fractionalLinear_eq h z]
  unfold denominator fractionalLinear at *
  have hM := Matrix.two_mul_expl g.1 h.1
  simp only [Matrix.SpecialLinearGroup.coe_mul, hM.2.2.1, hM.2.2.2, Int.cast_add, Int.cast_mul]
  field_simp [hNe] <;> ring

private theorem denominator_one (z : ℍ) : denominator 1 z = 1 := by
  simp [denominator, Matrix.SpecialLinearGroup.coe_one]

theorem squaredMultiplier_one : squaredMultiplier 1 = 1 := by
  have hEta := pow_ne_zero 2 (ModularForm.eta_ne_zero basePoint.im_pos)
  have h := eta_squared_transform 1 basePoint
  rw [one_smul, denominator_one, one_mul] at h
  exact mul_right_cancel₀ hEta (by simpa only [one_mul] using h.symm)

theorem squaredMultiplier_mul (g h : SL(2, ℤ)) :
    squaredMultiplier (g * h) = squaredMultiplier g * squaredMultiplier h := by
  let z := basePoint
  apply mul_right_cancel₀ (mul_ne_zero (denominator_ne_zero (g * h) z)
    (pow_ne_zero 2 (ModularForm.eta_ne_zero z.im_pos)))
  calc
    _ = ModularForm.eta (((g * h) • z : ℍ) : ℂ) ^ 2 := (eta_squared_transform (g * h) z).symm
    _ = _ := by
      rw [mul_smul, eta_squared_transform g (h • z), eta_squared_transform h z, denominator_mul]
      ring

theorem squaredMultiplier_S : squaredMultiplier ModularGroup.S = -Complex.I := by
  let z := basePoint
  have hEta := pow_ne_zero 2 (ModularForm.eta_ne_zero z.im_pos)
  have hS : ModularGroup.S • z = z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul]
    simp [z, basePoint, inv_neg]
  have hD : denominator ModularGroup.S z = Complex.I := by
    simp [denominator_eq, ModularGroup.denom_S, z, basePoint]
  have h := eta_squared_transform ModularGroup.S z
  rw [hS, hD] at h
  have hOne : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have hI : Complex.I * ModularForm.eta z ^ 2 ≠ 0 := mul_ne_zero Complex.I_ne_zero hEta
  apply mul_right_cancel₀ hI
  rw [h.symm, ← mul_assoc, hOne, one_mul]

theorem squaredMultiplier_T :
    squaredMultiplier ModularGroup.T =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 24) ^ 2 := by
  let z := basePoint
  have hEta := pow_ne_zero 2 (ModularForm.eta_ne_zero z.im_pos)
  have hT : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, ModularGroup.coe_T]
    simp
  have hD : denominator ModularGroup.T z = 1 := by
    simp [denominator, ModularGroup.coe_T]
  have h := eta_squared_transform ModularGroup.T z
  rw [hT, hD, one_mul] at h
  have hTranslation : ModularForm.eta ((z : ℂ) + 1) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 24) * ModularForm.eta z := by
    simpa only [Int.cast_one, mul_one] using Paper8ActualEtaTranslation.eta_add_integer z 1
  rw [hTranslation, mul_pow] at h
  exact mul_right_cancel₀ hEta h.symm

theorem squaredMultiplier_pow_twelve (g : SL(2, ℤ)) :
    squaredMultiplier g ^ 12 = 1 :=
  Paper8ActualEtaSquaredModularity.squaredMultiplier_pow_twelve g

theorem eta_pow_twentyFour_transform (g : SL(2, ℤ)) (z : ℍ) :
    ModularForm.eta ((g • z : ℍ) : ℂ) ^ 24 =
      denominator g z ^ 12 * ModularForm.eta z ^ 24 :=
  Paper8ActualEtaSquaredModularity.eta_pow_twentyFour_transform g z

end
end ManuscriptAudit.Paper8ActualEtaPowerModularity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualEtaPowerModularity.squaredMultiplier_one,
      ``ManuscriptAudit.Paper8ActualEtaPowerModularity.squaredMultiplier_mul,
      ``ManuscriptAudit.Paper8ActualEtaPowerModularity.squaredMultiplier_S,
      ``ManuscriptAudit.Paper8ActualEtaPowerModularity.squaredMultiplier_T,
      ``ManuscriptAudit.Paper8ActualEtaPowerModularity.squaredMultiplier_pow_twelve,
      ``ManuscriptAudit.Paper8ActualEtaPowerModularity.eta_pow_twentyFour_transform] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
