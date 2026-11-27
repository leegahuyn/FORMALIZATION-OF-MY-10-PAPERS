import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Trace

/-! For inverse group generators, the dual representation changes the Frobenius convention. -/

namespace ManuscriptAudit.FrobeniusDualConvention

open Module

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A group element acts on the dual by precomposition with its inverse. -/
def dualAction (e : V ≃ₗ[K] V) : Module.End K (Dual K V) :=
  e.symm.toLinearMap.dualMap

@[simp] theorem inverse_generator_on_dual (e : V ≃ₗ[K] V) :
    dualAction e.symm = e.toLinearMap.dualMap := by
  simp only [dualAction, LinearEquiv.symm_symm]

/-- The dual action of the inverse generator has the coefficients of the original point action. -/
theorem inverse_generator_coefficients (b : Basis (Fin 2) K V) (e : V ≃ₗ[K] V) :
    LinearMap.trace K (Dual K V) (dualAction e.symm) = LinearMap.trace K V e.toLinearMap ∧
      LinearMap.det (dualAction e.symm) = LinearMap.det e.toLinearMap := by
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  rw [inverse_generator_on_dual]
  exact ⟨LinearMap.trace_transpose' e.toLinearMap, LinearMap.det_dualMap e.toLinearMap⟩

theorem inverse_generator_charpoly (b : Basis (Fin 2) K V) (e : V ≃ₗ[K] V) :
    letI : Module.Free K V := Module.Free.of_basis b
    letI : Module.Finite K V := Module.Finite.of_basis b
    (dualAction e.symm).charpoly = e.toLinearMap.charpoly := by
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  rw [inverse_generator_on_dual, ← LinearMap.charpoly_toMatrix e.toLinearMap.dualMap b.dualBasis,
    ← LinearMap.charpoly_toMatrix e.toLinearMap b]
  change (LinearMap.toMatrix b.dualBasis b.dualBasis
    (Module.Dual.transpose (R := K) e.toLinearMap)).charpoly = _
  rw [LinearMap.toMatrix_transpose, Matrix.charpoly_transpose]

end
end ManuscriptAudit.FrobeniusDualConvention

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FrobeniusDualConvention.inverse_generator_on_dual,
      ``ManuscriptAudit.FrobeniusDualConvention.inverse_generator_coefficients,
      ``ManuscriptAudit.FrobeniusDualConvention.inverse_generator_charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
