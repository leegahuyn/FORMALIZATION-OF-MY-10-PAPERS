import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import PrimalitySheafVerification.ManuscriptAudit.RankTwoQuadraticOperator

/-! The reciprocal rank-two trace law computed with the actual characteristic polynomial. -/

namespace ManuscriptAudit.RankTwoInverseTrace

open Module Polynomial

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem determinant_mul_trace_inverse (b : Basis (Fin 2) K V) (e : V ≃ₗ[K] V) :
    LinearMap.det e.toLinearMap * LinearMap.trace K V e.symm.toLinearMap =
      LinearMap.trace K V e.toLinearMap := by
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  let f := e.toLinearMap
  let t := LinearMap.trace K V f
  let d := LinearMap.det f
  have hChar : f.charpoly = X^2 - C t * X + C d := by
    rw [← LinearMap.charpoly_toMatrix f b, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace K b, LinearMap.det_toMatrix b]
  have hPoly : f^2 - t • f + d • (1 : Module.End K V) = 0 := by
    have h := LinearMap.aeval_self_charpoly f
    rw [hChar] at h
    simpa only [map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul] using h
  have hInv : d • e.symm.toLinearMap = t • (1 : Module.End K V) - f := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun g : Module.End K V => g (e.symm x)) hPoly
    change e (e (e.symm x)) - t • e (e.symm x) + d • e.symm x = 0 at h
    rw [e.apply_symm_apply] at h
    change d • e.symm x = t • x - e x
    calc
      d • e.symm x = (e x - t • x + d • e.symm x) + (t • x - e x) := by abel
      _ = t • x - e x := by rw [h, zero_add]
  have hOne : LinearMap.trace K V (1 : Module.End K V) = 2 := by
    rw [LinearMap.trace_one, Module.finrank_eq_card_basis b, Fintype.card_fin] <;> norm_num
  have h := congrArg (LinearMap.trace K V) hInv
  simp only [map_smul, map_sub, smul_eq_mul, hOne] at h
  change d * LinearMap.trace K V e.symm.toLinearMap = t
  rw [h]
  change t * 2 - t = t
  ring

end
end ManuscriptAudit.RankTwoInverseTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.RankTwoInverseTrace.determinant_mul_trace_inverse
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
