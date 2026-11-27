import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! An operator conjugating a quadratic cyclotomic generator has trace zero over any scalar ring. -/

namespace ManuscriptAudit.CyclotomicConjugationTrace

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The cyclic-basis computation works in characteristic a power of two, without dividing by two. -/
theorem trace_det_of_cycle (B : Module.Basis (Fin 2) R V) (S F : V →ₗ[R] V)
    (hStep : S (B 0) = B 1) (hCube : S (S (S (B 0))) = B 0)
    (hQuad : S (S (B 0)) = -B 0 - B 1)
    (hConjugacy : F (S (B 0)) = S (S (F (B 0)))) :
    LinearMap.trace R V F = 0 ∧ ∃ a c : R, LinearMap.det F = -(a ^ 2 - a * c + c ^ 2) := by
  let M := LinearMap.toMatrix B B F
  let a := M 0 0
  let c := M 1 0
  have hF₀ : F (B 0) = a • B 0 + c • B 1 := by
    simpa only [M, a, c, LinearMap.toMatrix_apply, Fin.sum_univ_two] using
      (B.sum_repr (F (B 0))).symm
  have hSq₁ : S (S (B 1)) = B 0 := by rw [← hStep, hCube]
  have hF₁ : F (B 1) = (c - a) • B 0 + (-a) • B 1 := by
    calc
      _ = S (S (F (B 0))) := (congrArg F hStep).symm.trans hConjugacy
      _ = (S.comp S) (F (B 0)) := rfl
      _ = a • (-B 0 - B 1) + c • B 0 := by
        rw [hF₀, map_add, map_smul, map_smul]
        change a • S (S (B 0)) + c • S (S (B 1)) = _
        rw [hQuad, hSq₁]
      _ = _ := by
        simp only [smul_sub, smul_neg, sub_smul, neg_smul]
        abel
  have hM₁₁ : M 1 1 = -a := by
    change LinearMap.toMatrix B B F 1 1 = _
    simp [LinearMap.toMatrix_apply, hF₁]
  have hM₀₁ : M 0 1 = c - a := by
    change LinearMap.toMatrix B B F 0 1 = _
    simp [LinearMap.toMatrix_apply, hF₁]
  constructor
  · rw [LinearMap.trace_eq_matrix_trace R B]
    change M.trace = 0
    rw [Matrix.trace_fin_two, hM₁₁]
    exact add_neg_cancel a
  · refine ⟨a, c, ?_⟩
    rw [← LinearMap.det_toMatrix B]
    change M.det = _
    rw [Matrix.det_fin_two, hM₁₁, hM₀₁]
    change a * (-a) - (c - a) * c = _
    ring

end
end ManuscriptAudit.CyclotomicConjugationTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CyclotomicConjugationTrace.trace_det_of_cycle
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
