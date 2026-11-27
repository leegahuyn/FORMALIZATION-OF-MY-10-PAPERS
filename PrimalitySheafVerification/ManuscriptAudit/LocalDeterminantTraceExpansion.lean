import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Trace
import PrimalitySheafVerification.ManuscriptAudit.ComplexTriangularBasis
import PrimalitySheafVerification.ManuscriptAudit.LocalTriangularTraceDeterminant

/-! The genuine finite-dimensional local determinant has the convergent trace expansion. -/

namespace ManuscriptAudit.LocalDeterminantTraceExpansion

open Module ComplexTriangularBasis LocalTriangularTraceDeterminant

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def term (T : Module.End ℂ V) (z : ℂ) (n : ℕ) : ℂ :=
  z ^ (n + 1) * LinearMap.trace ℂ V (T ^ (n + 1)) / ((n + 1 : ℕ) : ℂ)

private theorem triangular_diag_isRoot {ι : Type} [Fintype ι] [LinearOrder ι]
    {M : Matrix ι ι ℂ} (hM : M.BlockTriangular id) (i : ι) :
    M.charpoly.IsRoot (M i i) := by
  have hScalar : (Matrix.scalar ι (M i i)).BlockTriangular id :=
    Matrix.blockTriangular_diagonal _
  change M.charpoly.eval (M i i) = 0
  rw [Matrix.eval_charpoly, Matrix.det_of_upperTriangular (hScalar.sub hM)]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [Matrix.sub_apply]

theorem native_det_trace_expansion (T : Module.End ℂ V) (z : ℂ)
    (hz : ∀ a : ℂ, T.HasEigenvalue a → ‖z * a‖ < 1) :
    Summable (term T z) ∧
      Complex.exp (∑' n : ℕ, term T z n) = (LinearMap.det ((1 : Module.End ℂ V) - z • T))⁻¹ := by
  obtain ⟨b, hb⟩ := exists_triangular_basis V T
  let Φ := LinearMap.toMatrixAlgEquiv b
  let M := LinearMap.toMatrix b b T
  have hM (i : Fin (finrank ℂ V)) : ‖z * M i i‖ < 1 := by
    apply hz
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← LinearMap.charpoly_toMatrix T b]
    exact triangular_diag_isRoot hb i
  have hp (n : ℕ) : LinearMap.toMatrix b b (T ^ n) = M ^ n := map_pow Φ T n
  have ht : term T z = traceTerm M z := by
    funext n
    rw [term, traceTerm, LinearMap.trace_eq_matrix_trace ℂ b, hp]
  have he : LinearMap.det ((1 : Module.End ℂ V) - z • T) =
      ((1 : Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ) - z • M).det := by
    rw [← LinearMap.det_toMatrix b]
    change (Φ ((1 : Module.End ℂ V) - z • T)).det = _
    rw [map_sub, map_one, map_smul] <;> rfl
  rw [ht, he]
  exact ⟨trace_series_summable hb z hM, exp_trace_series_eq_inverse_det hb z hM⟩

end
end ManuscriptAudit.LocalDeterminantTraceExpansion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.LocalDeterminantTraceExpansion.native_det_trace_expansion
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
