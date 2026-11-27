import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-! An explicit numerator for subtracting a point from its arithmetic Frobenius image. -/

namespace ManuscriptAudit.CubicFrobeniusDifferenceNumerator

open Polynomial

variable {F : Type*} [Field F]

/-- The chord numerator after clearing the square of the difference of abscissas. -/
def numerator (q k : ℕ) (A : F) : Polynomial F :=
  (X : Polynomial F) ^ (2 * q + 1) + X ^ (q + 2) + C (2 * A) +
    C 2 * (X ^ 3 + C A) ^ (k + 1)

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]

/-- Clearing denominators in the actual chord formula leaves a polynomial solely in the abscissa. -/
theorem chord_identity {k : ℕ} (hq : Fintype.card K = 2 * k + 1)
    (A : K) (x y : L) (h : y ^ 2 = x ^ 3 + algebraMap K L A) :
    (y ^ Fintype.card K + y) ^ 2 -
        (x ^ Fintype.card K + x) * (x ^ Fintype.card K - x) ^ 2 =
      (numerator (Fintype.card K) k (algebraMap K L A)).eval x := by
  let q := Fintype.card K
  let g := FiniteField.frobeniusAlgHom K L
  have hy := congrArg g h
  rw [map_pow, map_add, map_pow, AlgHom.commutes] at hy
  change (y ^ q) ^ 2 = (x ^ q) ^ 3 + algebraMap K L A at hy
  have hCross : y ^ q * y = (x ^ 3 + algebraMap K L A) ^ (k + 1) := by
    rw [← pow_succ y q]
    have hK : q + 1 = 2 * (k + 1) := by dsimp only [q]; omega
    rw [hK, pow_mul, h]
  have hX₁ : x ^ (2 * q + 1) = (x ^ q) ^ 2 * x := by
    rw [pow_succ, mul_comm 2 q, pow_mul]
  have hX₂ : x ^ (q + 2) = x ^ q * x ^ 2 := pow_add x q 2
  change (y ^ q + y) ^ 2 - (x ^ q + x) * (x ^ q - x) ^ 2 =
    (numerator q k (algebraMap K L A)).eval x
  rw [show (y ^ q + y) ^ 2 = (y ^ q) ^ 2 + 2 * (y ^ q * y) + y ^ 2 by ring,
    hy, hCross, h]
  simp only [numerator, eval_add, eval_mul, eval_pow, eval_X, eval_C, hX₁, hX₂]
  ring

/-- At each rational denominator root the numerator reduces to the quadratic character factor. -/
theorem eval_rational {k : ℕ} (A x : K) :
    (numerator (Fintype.card K) k A).eval x =
      2 * (x ^ 3 + A) * (1 + (x ^ 3 + A) ^ k) := by
  let q := Fintype.card K
  have hx : x ^ q = x := FiniteField.pow_card x
  have hX₁ : x ^ (2 * q + 1) = x ^ 3 := by
    rw [pow_succ, mul_comm 2 q, pow_mul, hx] <;> ring
  have hX₂ : x ^ (q + 2) = x ^ 3 := by
    rw [pow_add, hx] <;> ring
  change (numerator q k A).eval x = _
  simp only [numerator, eval_add, eval_mul, eval_pow, eval_X, eval_C, hX₁, hX₂]
  rw [pow_succ (x ^ 3 + A) k]
  ring

end ManuscriptAudit.CubicFrobeniusDifferenceNumerator

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFrobeniusDifferenceNumerator.chord_identity,
      ``ManuscriptAudit.CubicFrobeniusDifferenceNumerator.eval_rational] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
