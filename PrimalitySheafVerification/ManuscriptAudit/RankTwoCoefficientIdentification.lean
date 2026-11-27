import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.LinearCombination

/-! A root-free scalar quadratic uniquely determines rank-two operator coefficients. -/

namespace ManuscriptAudit.RankTwoCoefficientIdentification

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A scalar-root-free monic quadratic annihilator is the characteristic polynomial
of the actual rank-two matrix. -/
theorem matrix_trace_det (M : Matrix (Fin 2) (Fin 2) R) (a b : R)
    (hNo : ∀ r : R, r ^ 2 - a * r + b ≠ 0)
    (h : M ^ 2 - a • M + b • (1 : Matrix (Fin 2) (Fin 2) R) = 0) :
    M.trace = a ∧ M.det = b := by
  let x := M 0 0
  let y := M 0 1
  let z := M 1 0
  let w := M 1 1
  have h₀₀ : x * x + y * z - a * x + b = 0 := by
    simpa [x, y, z, w, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply] using congrFun (congrFun h 0) 0
  have h₀₁ : x * y + y * w - a * y = 0 := by
    simpa [x, y, z, w, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply] using congrFun (congrFun h 0) 1
  have h₁₀ : z * x + w * z - a * z = 0 := by
    simpa [x, y, z, w, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply] using congrFun (congrFun h 1) 0
  have ht : x + w = a := by
    by_contra hn
    have hP : x + w - a ≠ 0 := sub_ne_zero.mpr hn
    have hy : y = 0 := (mul_eq_zero.mp (show (x + w - a) * y = 0 by linear_combination h₀₁)).resolve_left hP
    have hz : z = 0 := (mul_eq_zero.mp (show (x + w - a) * z = 0 by linear_combination h₁₀)).resolve_left hP
    exact hNo x (by simpa only [pow_two, hy, hz, mul_zero, add_zero] using h₀₀)
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  change x + w = a ∧ x * w - y * z = b
  refine ⟨ht, ?_⟩
  rw [← ht] at h₀₀
  linear_combination -h₀₀

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The same coefficient identification for the actual linear operator in any rank-two basis. -/
theorem linear_trace_det (B : Module.Basis (Fin 2) R V) (F : Module.End R V) (a b : R)
    (hNo : ∀ r : R, r ^ 2 - a * r + b ≠ 0)
    (h : F ^ 2 - a • F + b • (1 : Module.End R V) = 0) :
    LinearMap.trace R V F = a ∧ LinearMap.det F = b := by
  let C := LinearMap.toMatrixAlgEquiv B
  have hM := congrArg C h
  simp only [map_pow, map_sub, map_add, map_smul, map_one, map_zero] at hM
  obtain ⟨ht, hd⟩ := matrix_trace_det (C F) a b hNo hM
  rw [LinearMap.trace_eq_matrix_trace R B, ← LinearMap.det_toMatrix B]
  exact ⟨ht, hd⟩

/-- The sole coefficients in the monic degree-two characteristic polynomial. -/
theorem linear_charpoly (B : Module.Basis (Fin 2) R V) (F : Module.End R V) (a b : R)
    (hNo : ∀ r : R, r ^ 2 - a * r + b ≠ 0)
    (h : F ^ 2 - a • F + b • (1 : Module.End R V) = 0) :
    letI : Module.Free R V := Module.Free.of_basis B
    letI : Module.Finite R V := Module.Finite.of_basis B
    F.charpoly = X ^ 2 - C a * X + C b := by
  letI : Module.Free R V := Module.Free.of_basis B
  letI : Module.Finite R V := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := linear_trace_det B F a b hNo h
  dsimp only
  rw [← LinearMap.charpoly_toMatrix _ B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace R B, LinearMap.det_toMatrix B, ht, hd]

end ManuscriptAudit.RankTwoCoefficientIdentification

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.RankTwoCoefficientIdentification.matrix_trace_det,
      ``ManuscriptAudit.RankTwoCoefficientIdentification.linear_trace_det,
      ``ManuscriptAudit.RankTwoCoefficientIdentification.linear_charpoly] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
