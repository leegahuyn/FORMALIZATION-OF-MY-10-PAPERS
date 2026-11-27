import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools

/-! A quadratic annihilating polynomial of a nonscalar rank-two endomorphism is its characteristic polynomial. -/

namespace ManuscriptAudit.RankTwoQuadraticOperator

open Polynomial Module

noncomputable section

variable {R V : Type*} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]
variable (B : Basis (Fin 2) R V) (S : Module.End R V)

include B

/-- A nonzero scalar multiple can be scalar only if the original endomorphism is scalar. -/
theorem scalar_of_linear_relation {a b : R} (hb : b ≠ 0)
    (h : a • (1 : Module.End R V) + b • S = 0) :
    ∃ c : R, S = c • (1 : Module.End R V) := by
  let M := LinearMap.toMatrix B B S
  have hM : a • (1 : Matrix (Fin 2) (Fin 2) R) + b • M = 0 := by
    simpa only [map_add, map_smul, map_zero, LinearMap.toMatrix_one] using
      congrArg (LinearMap.toMatrix B B) h
  have hEntry (i j : Fin 2) : a * (if i = j then 1 else 0) + b * M i j = 0 := by
    simpa only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, smul_eq_mul] using
      congrArg (fun N : Matrix (Fin 2) (Fin 2) R => N i j) hM
  have hDiag (i : Fin 2) : M i i = M 0 0 := by
    apply mul_left_cancel₀ hb
    have h₁ : a + b * M i i = 0 := by simpa using hEntry i i
    have h₀ : a + b * M 0 0 = 0 := by simpa using hEntry 0 0
    exact add_left_cancel (h₁.trans h₀.symm)
  have hScalar : M = (M 0 0) • (1 : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.one_apply] using hDiag i
    · have hh : b * M i j = 0 := by simpa [hij] using hEntry i j
      have hz := (mul_eq_zero.mp hh).resolve_left hb
      simp [Matrix.one_apply, hij, hz]
  refine ⟨M 0 0, ?_⟩
  apply (LinearMap.toMatrix B B).injective
  rw [map_smul, LinearMap.toMatrix_one]
  exact hScalar

theorem coefficients_zero_of_nonscalar
    (hS : ¬∃ c : R, S = c • (1 : Module.End R V)) {a b : R}
    (h : a • (1 : Module.End R V) + b • S = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra H
    exact hS (scalar_of_linear_relation B S H h)
  have hApply := congrArg (fun T : Module.End R V => T (B 0)) h
  change a • B 0 + b • S (B 0) = 0 at hApply
  rw [hb, zero_smul, add_zero] at hApply
  have ha := congrArg (fun v : V => B.repr v (0 : Fin 2)) hApply
  exact ⟨by simpa [Basis.repr_self] using ha, hb⟩

/-- The trace and determinant agree with the two coefficients of the actual quadratic identity. -/
theorem trace_det_of_quadratic
    (hS : ¬∃ c : R, S = c • (1 : Module.End R V)) (t d : R)
    (hQuad : S ^ 2 - t • S + d • (1 : Module.End R V) = 0) :
    LinearMap.trace R V S = t ∧ LinearMap.det S = d := by
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let t₀ := LinearMap.trace R V S
  let d₀ := LinearMap.det S
  have hChar : S.charpoly = X ^ 2 - C t₀ * X + C d₀ := by
    rw [← LinearMap.charpoly_toMatrix S B, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace R B, LinearMap.det_toMatrix B]
  have hCH := LinearMap.aeval_self_charpoly S
  rw [hChar] at hCH
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul] at hCH
  have hDiff : (d₀ - d) • (1 : Module.End R V) + (t - t₀) • S = 0 := by
    rw [sub_smul, sub_smul]
    calc
      _ = (S ^ 2 - t₀ • S + d₀ • (1 : Module.End R V)) -
          (S ^ 2 - t • S + d • (1 : Module.End R V)) := by abel
      _ = 0 := by rw [hCH, hQuad, sub_self]
  obtain ⟨hd, ht⟩ := coefficients_zero_of_nonscalar B S hS hDiff
  exact ⟨(sub_eq_zero.mp ht).symm, sub_eq_zero.mp hd⟩

end
end ManuscriptAudit.RankTwoQuadraticOperator

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.RankTwoQuadraticOperator.scalar_of_linear_relation,
      ``ManuscriptAudit.RankTwoQuadraticOperator.coefficients_zero_of_nonscalar,
      ``ManuscriptAudit.RankTwoQuadraticOperator.trace_det_of_quadratic] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
