import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The centralizer of a cyclic order-three companion operator in rank two. -/

namespace ManuscriptAudit.CubicRotationCentralizer

open Module Matrix

noncomputable section

variable {R V : Type*} [CommRing R] [Nontrivial R] [AddCommGroup V] [Module R V]
variable (B : Basis (Fin 2) R V) (S : Module.End R V)

theorem coefficients_unique (hS : S (B 0) = B 1) {a b c d : R}
    (h : a • (1 : Module.End R V) + b • S = c • 1 + d • S) :
    a = c ∧ b = d := by
  have hB : a • B 0 + b • B 1 = c • B 0 + d • B 1 := by
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.one_apply, hS] using
      congrArg (fun T : Module.End R V => T (B 0)) h
  constructor
  · simpa [Basis.repr_self] using congrArg (fun v : V => B.repr v (0 : Fin 2)) hB
  · simpa [Basis.repr_self] using congrArg (fun v : V => B.repr v (1 : Fin 2)) hB

/-- A commuting operator is a unique scalar linear combination of the identity and the rotation. -/
theorem exists_unique_coefficients (hS : S (B 0) = B 1) (F : Module.End R V)
    (hComm : F * S = S * F) :
    ∃! ab : R × R, F = ab.1 • (1 : Module.End R V) + ab.2 • S := by
  let a := B.repr (F (B 0)) 0
  let b := B.repr (F (B 0)) 1
  let T : Module.End R V := a • 1 + b • S
  have h₀ : F (B 0) = T (B 0) := by
    change F (B 0) = a • B 0 + b • S (B 0)
    rw [hS]
    have h : a • B 0 + b • B 1 = F (B 0) := by
      simpa only [Fin.sum_univ_two] using B.sum_repr (F (B 0))
    exact h.symm
  have hF (v : V) : F (S v) = S (F v) :=
    congrArg (fun U : Module.End R V => U v) hComm
  have hT (v : V) : T (S v) = S (T v) := by
    simp only [T, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.one_apply, map_add, map_smul]
  have h₁ : F (B 1) = T (B 1) := by rw [← hS, hF, h₀, hT]
  have hEq : F = T := by
    apply B.ext
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
  refine ⟨(a, b), hEq, fun cd hcd => ?_⟩
  exact Prod.ext (coefficients_unique B S hS (hcd.symm.trans hEq)).1
    (coefficients_unique B S hS (hcd.symm.trans hEq)).2

/-- The two coefficients have the ordinary quadratic trace and norm in the order-three basis. -/
theorem trace_det_of_form (h₀ : S (B 0) = B 1) (h₁ : S (B 1) = -B 0 - B 1)
    (a b : R) :
    LinearMap.trace R V (a • (1 : Module.End R V) + b • S) = 2 * a - b ∧
    LinearMap.det (a • (1 : Module.End R V) + b • S) = a ^ 2 - a * b + b ^ 2 := by
  let T : Module.End R V := a • 1 + b • S
  change LinearMap.trace R V T = _ ∧ LinearMap.det T = _
  have hMatrix : LinearMap.toMatrix B B T = !![a, -b; b, a - b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, LinearMap.toMatrix_apply, h₀, h₁, Basis.repr_self] <;> ring
  constructor
  · rw [LinearMap.trace_eq_matrix_trace R B, hMatrix, Matrix.trace, Fin.sum_univ_two]
    simp <;> ring
  · rw [← LinearMap.det_toMatrix B, hMatrix, Matrix.det_fin_two]
    simp <;> ring

end
end ManuscriptAudit.CubicRotationCentralizer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicRotationCentralizer.coefficients_unique,
      ``ManuscriptAudit.CubicRotationCentralizer.exists_unique_coefficients,
      ``ManuscriptAudit.CubicRotationCentralizer.trace_det_of_form] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
