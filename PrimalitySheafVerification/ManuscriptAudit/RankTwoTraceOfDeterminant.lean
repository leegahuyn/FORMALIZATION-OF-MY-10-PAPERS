import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel

/-! A nonzero known determinant and a quadratic annihilator identify the actual rank-two trace. -/

namespace ManuscriptAudit.RankTwoTraceOfDeterminant

open Polynomial Module

variable {R V : Type*} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]

/-- A rank-two operator with known nonzero determinant has the trace in any monic quadratic
annihilator with that constant term. -/
theorem trace_eq (B : Basis (Fin 2) R V) (F : Module.End R V) (a b : R)
    (hb : b ≠ 0) (hd : LinearMap.det F = b)
    (h : F ^ 2 - a • F + b • (1 : Module.End R V) = 0) :
    LinearMap.trace R V F = a := by
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let t := LinearMap.trace R V F
  have hChar : F.charpoly = X ^ 2 - C t * X + C b := by
    rw [← LinearMap.charpoly_toMatrix F B, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace R B, LinearMap.det_toMatrix B, hd]
  have hCH := LinearMap.aeval_self_charpoly F
  rw [hChar] at hCH
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul] at hCH
  have hRel : (t - a) • F = 0 := by
    rw [sub_smul]
    calc
      _ = (F ^ 2 - a • F + b • (1 : Module.End R V)) -
          (F ^ 2 - t • F + b • (1 : Module.End R V)) := by abel
      _ = _ := by rw [h, hCH, sub_self]
  have hRank : finrank R V = 2 := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  have hD := congrArg LinearMap.det hRel
  rw [LinearMap.det_smul, hRank, hd, LinearMap.det_zero' B] at hD
  have hZ := (mul_eq_zero.mp hD).resolve_right hb
  by_contra he
  exact pow_ne_zero 2 (sub_ne_zero.mpr he) hZ

end ManuscriptAudit.RankTwoTraceOfDeterminant

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RankTwoTraceOfDeterminant.trace_eq
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
