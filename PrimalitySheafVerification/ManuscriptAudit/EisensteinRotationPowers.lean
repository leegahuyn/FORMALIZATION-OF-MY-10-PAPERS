import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.EisensteinPowerCongruence
import PrimalitySheafVerification.ManuscriptAudit.RotationNormUnit
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedRecurrence

/-! The integer coefficient progression agrees with actual rotation endomorphism powers and arithmetic traces. -/

namespace ManuscriptAudit.EisensteinRotationPowers

open EisensteinPowerCongruence RotationNormUnit CubicRotationCombination Paper5PrintedRecurrence

section Ring

variable {R : Type*} [Ring R]

theorem combination_mul (r : R) (hr : r ^ 2 + r + 1 = 0) (a b c d : ℤ) :
    combination r a b * combination r c d =
      combination r (a * c - b * d) (a * d + b * c - b * d) := by
  have hZ (n : ℤ) (x y : R) : (n • x) * y = n • (x * y) := by
    let f : R →+ R :=
      { toFun := fun z => z * y
        map_zero' := zero_mul y
        map_add' := fun _ _ => add_mul _ _ _ }
    exact map_zsmul f n x
  simp only [combination]
  rw [add_mul, hZ, hZ, one_mul, rotation_mul_linear r hr c d]
  simp only [zsmul_add, ← mul_zsmul]
  simp only [mul_neg, mul_sub, sub_zsmul, add_zsmul, neg_zsmul] <;> abel

/-- The arithmetic pair represents the actual n-th power of the native rotation combination. -/
theorem combination_pow (r : R) (hr : r ^ 2 + r + 1 = 0) (a b : ℤ) (n : ℕ) :
    combination r a b ^ n =
      combination r (coefficients a b n).1 (coefficients a b n).2 := by
  induction n with
  | zero => simp [coefficients, combination]
  | succ n ih =>
      rw [pow_succ, ih, combination_mul r hr]
      rfl

end Ring

theorem norm_coefficients (a b : ℤ) (n : ℕ) :
    let v := coefficients a b n
    v.1 ^ 2 - v.1 * v.2 + v.2 ^ 2 = (a ^ 2 - a * b + b ^ 2) ^ n := by
  let v := coefficients a b n
  change v.1 ^ 2 - v.1 * v.2 + v.2 ^ 2 = _
  calc
    _ = (matrix v.1 v.2).det := (det_matrix _ _).symm
    _ = _ := by rw [show matrix v.1 v.2 = matrix a b ^ n from (matrix_power a b n).symm,
      Matrix.det_pow, det_matrix]

theorem trace_coefficients (a b : ℤ) (q : ℕ) (h : a ^ 2 - a * b + b ^ 2 = (q : ℤ))
    (n : ℕ) : 2 * (coefficients a b n).1 - (coefficients a b n).2 =
      recurrence q (2 * a - b) n := by
  let T (i : ℕ) := 2 * (coefficients a b i).1 - (coefficients a b i).2
  change T n = _
  have hStep (i : ℕ) : T (i + 2) = (2 * a - b) * T (i + 1) -
      (a ^ 2 - a * b + b ^ 2) * T i := by
    dsimp only [T, coefficients]
    ring
  induction n using Nat.twoStepInduction with
  | zero => simp [T, coefficients, recurrence]
  | one => simp [T, coefficients, recurrence]
  | more i ih ih' => rw [hStep, h, ih, ih', recurrence]

/-- Norm of the difference from one is the actual point-count recurrence value. -/
theorem difference_norm_eq_count (a b : ℤ) (q : ℕ)
    (h : a ^ 2 - a * b + b ^ 2 = (q : ℤ)) (n : ℕ) :
    let v := coefficients a b n
    (v.1 - 1) ^ 2 - (v.1 - 1) * v.2 + v.2 ^ 2 =
      ((q ^ n : ℕ) : ℤ) + 1 - recurrence q (2 * a - b) n := by
  let v := coefficients a b n
  change (v.1 - 1) ^ 2 - (v.1 - 1) * v.2 + v.2 ^ 2 = _
  have hn : v.1 ^ 2 - v.1 * v.2 + v.2 ^ 2 = (a ^ 2 - a * b + b ^ 2) ^ n :=
    norm_coefficients a b n
  have ht : 2 * v.1 - v.2 = recurrence q (2 * a - b) n := trace_coefficients a b q h n
  calc
    _ = (v.1 ^ 2 - v.1 * v.2 + v.2 ^ 2) + 1 - (2 * v.1 - v.2) := by ring
    _ = _ := by rw [hn, ht, h, Nat.cast_pow]

end ManuscriptAudit.EisensteinRotationPowers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.EisensteinRotationPowers.combination_pow,
      ``ManuscriptAudit.EisensteinRotationPowers.difference_norm_eq_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
