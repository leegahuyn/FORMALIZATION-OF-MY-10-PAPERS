import Lean.Util.CollectAxioms
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Lifting a stabilized transition matrix

For a surjective ring map, the block diagonal matrix with an invertible
matrix and its inverse on the diagonal lifts to an invertible matrix.
The proof factors it into three block transvections and a signed rotation.
-/

namespace ManuscriptAudit.MilnorStabilizedMatrix

open Matrix

universe u v

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {R : Type v} [CommRing R]

private def upper (M : Matrix n n R) : GL (n ⊕ n) R where
  val := fromBlocks 1 M 0 1
  inv := fromBlocks 1 (-M) 0 1
  val_inv := by simp [fromBlocks_multiply]
  inv_val := by simp [fromBlocks_multiply]

private def lower (M : Matrix n n R) : GL (n ⊕ n) R where
  val := fromBlocks 1 0 M 1
  inv := fromBlocks 1 0 (-M) 1
  val_inv := by simp [fromBlocks_multiply]
  inv_val := by simp [fromBlocks_multiply]

private def rotation (n : Type u) [Fintype n] [DecidableEq n]
    (R : Type v) [CommRing R] : GL (n ⊕ n) R where
  val := fromBlocks 0 (-1) 1 0
  inv := fromBlocks 0 1 (-1) 0
  val_inv := by simp [fromBlocks_multiply]
  inv_val := by simp [fromBlocks_multiply]

/-- The block diagonal unit with `U` and its inverse as its blocks. -/
def stabilized (U : GL n R) : GL (n ⊕ n) R where
  val := fromBlocks U.val 0 0 U.inv
  inv := fromBlocks U.inv 0 0 U.val
  val_inv := by simp [fromBlocks_multiply, U.val_inv, U.inv_val]
  inv_val := by simp [fromBlocks_multiply, U.val_inv, U.inv_val]

private theorem factorization (U : GL n R) :
    upper U.val * lower (-U.inv) * upper U.val * rotation n R = stabilized U := by
  apply Units.ext
  change fromBlocks 1 U.val 0 1 * fromBlocks 1 0 (-U.inv) 1 *
      fromBlocks 1 U.val 0 1 * fromBlocks 0 (-1) 1 0 =
    fromBlocks U.val 0 0 U.inv
  simp [fromBlocks_multiply, U.val_inv, U.inv_val, mul_neg, neg_mul]

variable {D : Type v} [CommRing D] (q : R →+* D)

private theorem map_one_matrix : (1 : Matrix n n R).map q = (1 : Matrix n n D) :=
  (q.mapMatrix : Matrix n n R →+* Matrix n n D).map_one

private theorem map_zero_matrix : (0 : Matrix n n R).map q = (0 : Matrix n n D) :=
  (q.mapMatrix : Matrix n n R →+* Matrix n n D).map_zero

private theorem map_neg_one_matrix : (-1 : Matrix n n R).map q = (-1 : Matrix n n D) := by
  change (q.mapMatrix : Matrix n n R →+* Matrix n n D) (-1) = -1
  rw [map_neg, map_one]

private theorem map_upper (M : Matrix n n R) :
    GeneralLinearGroup.map q (upper M) = upper (M.map q) := by
  apply Units.ext
  change (fromBlocks 1 M 0 1).map q = fromBlocks 1 (M.map q) 0 1
  simp only [fromBlocks_map, map_one_matrix, map_zero_matrix]

private theorem map_lower (M : Matrix n n R) :
    GeneralLinearGroup.map q (lower M) = lower (M.map q) := by
  apply Units.ext
  change (fromBlocks 1 0 M 1).map q = fromBlocks 1 0 (M.map q) 1
  simp only [fromBlocks_map, map_one_matrix, map_zero_matrix]

private theorem map_rotation :
    GeneralLinearGroup.map q (rotation n R) = rotation n D := by
  apply Units.ext
  change (fromBlocks (0 : Matrix n n R) (-1) 1 0).map q =
    fromBlocks (0 : Matrix n n D) (-1) 1 0
  simp only [fromBlocks_map, map_one_matrix, map_zero_matrix, map_neg_one_matrix]

private theorem map_matrix_surjective (hq : Function.Surjective q) :
    Function.Surjective (fun A : Matrix n n R => A.map q) := by
  intro M
  let A : Matrix n n R := Matrix.of fun i j => Classical.choose (hq (M i j))
  refine ⟨A, Matrix.ext fun i j => ?_⟩
  change q (Classical.choose (hq (M i j))) = M i j
  exact Classical.choose_spec (hq (M i j))

/-- Stabilization of an invertible matrix lifts through every surjective ring map. -/
theorem stabilized_lifts (hq : Function.Surjective q) (U : GL n D) :
    ∃ V : GL (n ⊕ n) R, GeneralLinearGroup.map q V = stabilized U := by
  obtain ⟨A, hA⟩ := map_matrix_surjective q hq U.val
  obtain ⟨C, hC⟩ := map_matrix_surjective q hq (-U.inv)
  refine ⟨upper A * lower C * upper A * rotation n R, ?_⟩
  simp only [map_mul, map_upper, map_lower, map_rotation, hA, hC, factorization]

/-- The lifted unit has the requested entrywise reduction on the full block matrix. -/
theorem stabilized_matrix_lifts (hq : Function.Surjective q) (U : GL n D) :
    ∃ V : GL (n ⊕ n) R, V.val.map q = fromBlocks U.val 0 0 U.inv := by
  obtain ⟨V, hV⟩ := stabilized_lifts q hq U
  exact ⟨V, congrArg Units.val hV⟩

end ManuscriptAudit.MilnorStabilizedMatrix

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MilnorStabilizedMatrix.stabilized_lifts,
      ``ManuscriptAudit.MilnorStabilizedMatrix.stabilized_matrix_lifts] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
