import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Ring

/-! Exact Euler determinant for a rank-two module over an arbitrary commutative ring. -/

namespace ManuscriptAudit.RankTwoEulerDeterminant

open Module

noncomputable section

variable {R : Type*} [CommRing R]

theorem matrix_determinant (M : Matrix (Fin 2) (Fin 2) R) (z : R) :
    ((1 : Matrix (Fin 2) (Fin 2) R)-z • M).det =
      1-z*M.trace+z^2*M.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]
  simp [Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply] <;> ring

theorem linear_determinant {V : Type*} [AddCommGroup V] [Module R V]
    (B : Basis (Fin 2) R V) (F : Module.End R V) (z : R) :
    LinearMap.det ((1 : Module.End R V)-z • F) =
      1-z*LinearMap.trace R V F+z^2*LinearMap.det F := by
  let M := LinearMap.toMatrix B B F
  have h : LinearMap.toMatrix B B ((1 : Module.End R V)-z • F) =
      (1 : Matrix (Fin 2) (Fin 2) R)-z • M := by
    let Φ := LinearMap.toMatrixAlgEquiv B
    change Φ ((1 : Module.End R V)-z • F) = 1-z • Φ F
    rw [map_sub, map_one, map_smul]
  rw [← LinearMap.det_toMatrix B, LinearMap.trace_eq_matrix_trace R B,
    ← LinearMap.det_toMatrix B F, h]
  exact matrix_determinant M z

end
end ManuscriptAudit.RankTwoEulerDeterminant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RankTwoEulerDeterminant.matrix_determinant,
      ``ManuscriptAudit.RankTwoEulerDeterminant.linear_determinant] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
