import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Integral Eisenstein power coefficients eventually return to (1,0) modulo each unit modulus. -/

namespace ManuscriptAudit.EisensteinPowerCongruence

open Matrix

section Matrix

variable {R : Type*} [CommRing R]

def matrix (a b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, -b; b, a - b]

@[simp] theorem matrix_one : matrix (1 : R) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, Matrix.one_apply]

theorem matrix_mul (a b c d : R) :
    matrix a b * matrix c d = matrix (a * c - b * d) (a * d + b * c - b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_matrix (a b : R) : (matrix a b).det = a ^ 2 - a * b + b ^ 2 := by
  rw [matrix, Matrix.det_fin_two_of]
  ring

end Matrix

def coefficients (a b : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
      let v := coefficients a b n
      (v.1 * a - v.2 * b, v.1 * b + v.2 * a - v.2 * b)

theorem matrix_power {R : Type*} [CommRing R] (a b : ℤ) (n : ℕ) :
    matrix (a : R) (b : R) ^ n =
      matrix ((coefficients a b n).1 : R) ((coefficients a b n).2 : R) := by
  induction n with
  | zero => simp [coefficients]
  | succ n ih =>
      rw [pow_succ, ih, matrix_mul]
      simp only [coefficients, Int.cast_sub, Int.cast_mul, Int.cast_add]

/-- The coefficient pair of a positive power can be made congruent to (1,0). -/
theorem exists_positive_power {m : ℕ} [NeZero m] (a b : ℤ)
    (h : IsUnit ((a ^ 2 - a * b + b ^ 2 : ℤ) : ZMod m)) :
    ∃ n : ℕ, 0 < n ∧ ((coefficients a b n).1 : ZMod m) = 1 ∧
      ((coefficients a b n).2 : ZMod m) = 0 := by
  let M := Matrix (Fin 2) (Fin 2) (ZMod m)
  let A := matrix (a : ZMod m) (b : ZMod m)
  have hDet : IsUnit A.det := by
    rw [det_matrix]
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow] using h
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hDet
  haveI : Finite Mˣ := Finite.of_injective (fun v : Mˣ => (v : M)) Units.val_injective
  let n := orderOf u
  have hn : 0 < n := orderOf_pos u
  have hA : A ^ n = 1 := by
    rw [← hu]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun v : Mˣ => (v : M)) (pow_orderOf_eq_one u)
  rw [matrix_power] at hA
  refine ⟨n, hn, ?_, ?_⟩
  · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 0 0) hA
  · have hb := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 0) hA
    change ((coefficients a b n).2 : ZMod m) = (1 : Matrix (Fin 2) (Fin 2) (ZMod m)) 1 0 at hb
    simpa only [Matrix.one_apply, show (1 : Fin 2) ≠ 0 by decide, if_false] using hb

end ManuscriptAudit.EisensteinPowerCongruence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EisensteinPowerCongruence.exists_positive_power
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
