import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-! Multiplication by each cubic rotation preserves the two integral coefficients. -/

namespace ManuscriptAudit.CubicRotationCombination

def rotatedCoefficients (n : Fin 3) (a b : ℤ) : ℤ × ℤ :=
  if n = 0 then (a, b)
  else if n = 1 then (-b, a - b)
  else (b - a, -a)

variable {R : Type*} [Ring R]

theorem rotation_mul_linear (r : R) (hr : r ^ 2 + r + 1 = 0) (a b : ℤ) :
    r * (a • (1 : R) + b • r) = (-b) • (1 : R) + (a - b) • r := by
  have h₂ : r ^ 2 = -r - 1 := by
    calc
      r ^ 2 = (r ^ 2 + r + 1) - r - 1 := by abel
      _ = -r - 1 := by rw [hr, zero_sub]
  rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, ← pow_two, h₂, smul_sub, smul_neg,
    neg_smul, sub_smul]
  abel

theorem rotation_pow_linear (r : R) (hr : r ^ 2 + r + 1 = 0) (n : Fin 3) (a b : ℤ) :
    r ^ n.val * (a • (1 : R) + b • r) =
      (rotatedCoefficients n a b).1 • (1 : R) + (rotatedCoefficients n a b).2 • r := by
  fin_cases n
  · change r ^ 0 * (a • (1 : R) + b • r) = a • (1 : R) + b • r
    rw [pow_zero, one_mul]
  · change r ^ 1 * (a • (1 : R) + b • r) = (-b) • (1 : R) + (a - b) • r
    rw [pow_one, rotation_mul_linear r hr]
  · change r ^ 2 * (a • (1 : R) + b • r) = (b - a) • (1 : R) + (-a) • r
    rw [pow_two, mul_assoc, rotation_mul_linear r hr a b, rotation_mul_linear r hr (-b) (a - b)]
    rw [show -(a - b) = b - a by abel, show -b - (a - b) = -a by abel]

end ManuscriptAudit.CubicRotationCombination

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicRotationCombination.rotation_mul_linear,
      ``ManuscriptAudit.CubicRotationCombination.rotation_pow_linear] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
