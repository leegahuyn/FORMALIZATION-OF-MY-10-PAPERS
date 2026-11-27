import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.RotationNormUnit

/-! Factorization of the split cubic arithmetic polynomial with its two Eisenstein orientations. -/

namespace ManuscriptAudit.EisensteinCharacteristicFactorization

open RotationNormUnit

variable {R : Type*} [Ring R]

/-- The two orientations have the same scalar trace. -/
theorem combination_add_conjugate (r : R) (a b : ℤ) :
    combination r a b + combination r (a - b) (-b) = (2 * a - b) • (1 : R) := by
  calc
    _ = (a • (1 : R) + (a - b) • (1 : R)) + (b • r + (-b) • r) := by
      simp only [combination]
      abel
    _ = _ := by
      rw [← add_zsmul, ← add_zsmul, add_neg_cancel, zero_zsmul, add_zero]
      congr 1
      ring

/-- Expand the two actual endomorphism factors using the rotation relation. -/
theorem factor (f r : R) (hr : r ^ 2 + r + 1 = 0) (hf : Commute f r) (a b : ℤ) :
    (f - combination r a b) * (f - combination r (a - b) (-b)) =
      f ^ 2 - (2 * a - b) • f + (a ^ 2 - a * b + b ^ 2) • (1 : R) := by
  let u := combination r a b
  let v := combination r (a - b) (-b)
  have hv : f * v = v * f := by
    simp only [v, combination, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      one_mul, hf.eq]
  change (f - u) * (f - v) = _
  rw [mul_sub, sub_mul, sub_mul, ← pow_two, hv]
  calc
    _ = f ^ 2 - (u * f + v * f) + u * v := by abel
    _ = _ := by
      rw [← add_mul, combination_add_conjugate r a b, smul_mul_assoc, one_mul,
        combination_mul_conjugate r hr a b]

/-- Conjugating the orientation preserves both integral coefficients of the quadratic. -/
theorem conjugate_coefficients (a b : ℤ) :
    2 * (a - b) - (-b) = 2 * a - b ∧
      (a - b) ^ 2 - (a - b) * (-b) + (-b) ^ 2 = a ^ 2 - a * b + b ^ 2 := by
  constructor <;> ring

end ManuscriptAudit.EisensteinCharacteristicFactorization

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.EisensteinCharacteristicFactorization.combination_add_conjugate,
      ``ManuscriptAudit.EisensteinCharacteristicFactorization.factor,
      ``ManuscriptAudit.EisensteinCharacteristicFactorization.conjugate_coefficients] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
