import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! Units of Eisenstein norm act invertibly in any finite-torsion representation of a cube rotation. -/

namespace ManuscriptAudit.RotationNormUnit

open Polynomial

section Ring

variable {R : Type*} [Ring R]

def combination (r : R) (a b : ℤ) : R :=
  a • (1 : R) + b • r

private theorem eval_linear (r : R) (a b : ℤ) :
    (aeval r : ℤ[X] →ₐ[ℤ] R) (C a + C b * X) = combination r a b := by
  simp [combination, algebraMap_int_eq, zsmul_eq_mul]

/-- Multiplying by the conjugate rotation combination gives scalar multiplication by its norm. -/
theorem combination_mul_conjugate (r : R) (hr : r ^ 2 + r + 1 = 0) (a b : ℤ) :
    combination r a b * combination r (a - b) (-b) = (a ^ 2 - a * b + b ^ 2) • (1 : R) := by
  let f : ℤ[X] →ₐ[ℤ] R := aeval r
  have h :
      (C a + C b * X) * (C (a - b) + C (-b) * X) =
        (C (a ^ 2 - a * b + b ^ 2) + C (-(b ^ 2)) * (X ^ 2 + X + 1) : ℤ[X]) := by
    simp only [map_sub, map_mul, map_add, map_pow, map_neg]
    ring
  calc
    _ = f ((C a + C b * X) * (C (a - b) + C (-b) * X)) := by
      rw [map_mul, show f (C a + C b * X) = combination r a b from eval_linear r a b,
        show f (C (a - b) + C (-b) * X) = combination r (a - b) (-b) from
          eval_linear r (a - b) (-b)]
    _ = f (C (a ^ 2 - a * b + b ^ 2) + C (-(b ^ 2)) * (X ^ 2 + X + 1)) := congrArg f h
    _ = _ := by
      simpa only [f, map_add, map_mul, map_pow, map_one, aeval_C, aeval_X, hr, mul_zero,
        add_zero, algebraMap_int_eq, Int.castRingHom_apply, zsmul_eq_mul, mul_one]

theorem combination_commute (r : R) (a b c d : ℤ) :
    Commute (combination r a b) (combination r c d) := by
  let f : ℤ[X] →ₐ[ℤ] R := aeval r
  let P : ℤ[X] := C a + C b * X
  let Q : ℤ[X] := C c + C d * X
  have hp : f P = combination r a b := eval_linear r a b
  have hq : f Q = combination r c d := eval_linear r c d
  rw [← hp, ← hq]
  exact show f P * f Q = f Q * f P from
    ((map_mul f P Q).symm.trans (congrArg f (mul_comm P Q))).trans (map_mul f Q P)

end Ring

variable {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod m) V]

/-- A rotation combination whose norm is a unit modulo m is an invertible endomorphism. -/
theorem isUnit_of_norm (r : Module.End (ZMod m) V) (hr : r ^ 2 + r + 1 = 0) (a b : ℤ)
    (hn : IsUnit ((a ^ 2 - a * b + b ^ 2 : ℤ) : ZMod m)) :
    IsUnit (combination r a b) := by
  have h := hn.map (algebraMap (ZMod m) (Module.End (ZMod m) V))
  rw [map_intCast] at h
  have h' : IsUnit ((a ^ 2 - a * b + b ^ 2 : ℤ) • (1 : Module.End (ZMod m) V)) := by
    simpa only [zsmul_eq_mul, mul_one] using h
  exact ((combination_commute r a b (a - b) (-b)).isUnit_mul_iff.mp
    ((combination_mul_conjugate r hr a b).symm ▸ h')).1

end ManuscriptAudit.RotationNormUnit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RotationNormUnit.isUnit_of_norm
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
