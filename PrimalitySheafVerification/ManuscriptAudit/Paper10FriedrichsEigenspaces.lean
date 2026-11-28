import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Spectrum
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsCompact

/-! Multiplicities and completeness for the actual partial operator associated
with a compact Hilbert form embedding. -/

namespace ManuscriptAudit.Paper10FriedrichsEigenspaces

open Module.End Paper10FriedrichsResolvent Paper10FriedrichsCompact

noncomputable section

variable {𝕜 D H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

variable (J : D →L[𝕜] H)

def operatorEigenspace (λ : 𝕜) : Submodule 𝕜 H :=
  (realization J).graph.comap ((LinearMap.id : H →ₗ[𝕜] H).prod (λ • LinearMap.id))

/-- The actual operator eigenspace agrees with the corresponding bounded resolvent eigenspace. -/
theorem eigenspace_reciprocity (hJ : DenseRange J) (λ : 𝕜) (hλ : λ ≠ 0) :
    operatorEigenspace J λ = eigenspace (resolvent J).toLinearMap λ⁻¹ := by
  apply Submodule.ext
  intro x
  change (x, λ • x) ∈ (realization J).graph ↔ _
  rw [eigenvector_reciprocity J hJ λ hλ x, mem_eigenspace_iff]

theorem zero_eigenspace (hJ : DenseRange J) : operatorEigenspace J 0 = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change (x, (0 : 𝕜) • x) ∈ (realization J).graph at hx
  have e := (realization_graph_iff J hJ x ((0 : 𝕜) • x)).mp hx
  simpa only [zero_smul, map_zero, Submodule.mem_bot] using e.symm

/-- Each eigenspace has finite dimension with the actual multiplicity space. -/
theorem finite_multiplicity (hJ : DenseRange J) (hK : IsCompactOperator J) (λ : 𝕜) :
    FiniteDimensional 𝕜 (operatorEigenspace J λ) := by
  by_cases hλ : λ = 0
  · rw [hλ, zero_eigenspace J hJ]
    infer_instance
  · rw [eigenspace_reciprocity J hJ λ hλ]
    exact ContinuousLinearMap.finite_dimensional_eigenspace (compact_resolvent J hK) _
      (inv_ne_zero hλ)

/-- The span of all true eigenvectors of the actual partial operator is dense. -/
theorem eigenspaces_dense (hJ : DenseRange J) (hK : IsCompactOperator J) :
    (⨆ λ, operatorEigenspace J λ).topologicalClosure = ⊤ := by
  let B := resolvent J
  have hB : B.IsSymmetric := resolvent_symmetric J
  have hComplete := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (compact_resolvent J hK) hB
  have hLe : (⨆ μ, eigenspace B.toLinearMap μ) ≤ ⨆ λ, operatorEigenspace J λ := by
    apply iSup_le
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      have hZero : eigenspace B.toLinearMap 0 = ⊥ := by
        apply le_antisymm _ bot_le
        intro x hx
        have hx₀ : x ∈ B.ker := by
          change B x = 0
          simpa only [zero_smul] using (mem_eigenspace_iff.mp hx)
        rwa [show B.ker = ⊥ from resolvent_ker J hJ] at hx₀
      rw [hZero]
      exact bot_le
    · have h := eigenspace_reciprocity J hJ μ⁻¹ (inv_ne_zero hμ)
      rw [inv_inv] at h
      rw [← h]
      exact le_iSup (operatorEigenspace J) μ⁻¹
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  have hOrth := Submodule.orthogonal_le hLe
  rw [hComplete] at hOrth
  exact le_antisymm hOrth bot_le

end
end ManuscriptAudit.Paper10FriedrichsEigenspaces

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsEigenspaces.eigenspace_reciprocity,
      ``ManuscriptAudit.Paper10FriedrichsEigenspaces.finite_multiplicity,
      ``ManuscriptAudit.Paper10FriedrichsEigenspaces.eigenspaces_dense] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
