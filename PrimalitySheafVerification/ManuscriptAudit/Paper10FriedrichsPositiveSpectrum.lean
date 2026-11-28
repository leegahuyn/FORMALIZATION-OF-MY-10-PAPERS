import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsCompact

/-! The genuinely realized positive real form has strictly positive eigenvalues. -/

namespace ManuscriptAudit.Paper10FriedrichsPositiveSpectrum

open Paper10FriedrichsResolvent Paper10FriedrichsCompact
open scoped RealInnerProductSpace

noncomputable section

variable {D H : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every nonzero eigenvector of the unbounded positive realization has a positive energy. -/
theorem eigenvalue_pos (J : D →L[ℝ] H) (hJ : DenseRange J) {x : H} (hx : x ≠ 0)
    {e : ℝ} (h : (x,e • x) ∈ (realization J).graph) : 0 < e := by
  have he : e ≠ 0 := by
    intro he
    subst e
    have z := (realization_graph_iff J hJ x ((0 : ℝ) • x)).mp h
    rw [zero_smul, map_zero] at z
    exact hx z.symm
  have hAdj : J.adjoint x ≠ 0 := by
    intro hy
    have hmem : x ∈ (resolvent J).ker := by
      change J (J.adjoint x) = 0
      rw [hy, map_zero]
    rw [resolvent_ker J hJ, Submodule.mem_bot] at hmem
    exact hx hmem
  have hP : 0 < ⟪resolvent J x,x⟫ := by
    change 0 < ⟪J (J.adjoint x),x⟫
    rw [← J.adjoint_inner_right, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hAdj) 2
  have hR := (eigenvector_reciprocity J hJ e he x).mp h
  rw [hR, real_inner_smul_left, real_inner_self_eq_norm_sq] at hP
  exact inv_pos.mp ((mul_pos_iff_of_pos_right (pow_pos (norm_pos_iff.mpr hx) 2)).mp hP)

end
end ManuscriptAudit.Paper10FriedrichsPositiveSpectrum

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10FriedrichsPositiveSpectrum.eigenvalue_pos
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
