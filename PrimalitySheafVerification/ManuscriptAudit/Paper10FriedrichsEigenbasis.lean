import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.l2Space
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsEigenspaces

/-! Every compact form embedding yields a genuine orthonormal eigenbasis
in the Hilbert space of the actual partial operator. -/

namespace ManuscriptAudit.Paper10FriedrichsEigenbasis

open Module.End Paper10FriedrichsResolvent Paper10FriedrichsEigenspaces
open scoped InnerProductSpace

noncomputable section

variable {𝕜 D H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

variable (J : D →L[𝕜] H)

theorem different_eigenspaces_orthogonal (hJ : DenseRange J)
    {λ μ : 𝕜} (h : λ ≠ μ) {x y : H}
    (hx : x ∈ operatorEigenspace J λ) (hy : y ∈ operatorEigenspace J μ) :
    ⟪x, y⟫_𝕜 = 0 := by
  by_cases hλ : λ = 0
  · subst λ
    have hx₀ : x = 0 := by rwa [zero_eigenspace J hJ, Submodule.mem_bot] at hx
    rw [hx₀, inner_zero_left]
  by_cases hμ : μ = 0
  · subst μ
    have hy₀ : y = 0 := by rwa [zero_eigenspace J hJ, Submodule.mem_bot] at hy
    rw [hy₀, inner_zero_right]
  rw [eigenspace_reciprocity J hJ λ hλ] at hx
  rw [eigenspace_reciprocity J hJ μ hμ] at hy
  have hB : (resolvent J).toLinearMap.IsSymmetric := resolvent_symmetric J
  exact hB.orthogonalFamily_eigenspaces (fun e => h (inv_injective e)) ⟨x, hx⟩ ⟨y, hy⟩

abbrev EigenIndex := Σ λ : 𝕜, Fin (Module.finrank 𝕜 (operatorEigenspace J λ))

/-- There is an orthonormal Hilbert basis on the true graph, with the
finite-dimensional multiplicity of each eigenvalue built into its indices. -/
theorem exists_eigenbasis (hJ : DenseRange J) (hK : IsCompactOperator J) :
    ∃ b : HilbertBasis (EigenIndex J) 𝕜 H,
      ∀ i, (b i, i.1 • b i) ∈ (realization J).graph := by
  classical
  letI (λ : 𝕜) := finite_multiplicity J hJ hK λ
  let b (λ : 𝕜) := stdOrthonormalBasis 𝕜 (operatorEigenspace J λ)
  let v (i : EigenIndex J) : H := (b i.1 i.2).val
  have hOrtho : Orthonormal 𝕜 v := by
    constructor
    · rintro ⟨λ, i⟩
      exact (b λ).orthonormal.1 i
    · rintro ⟨λ, i⟩ ⟨μ, j⟩ h
      by_cases h' : λ = μ
      · subst μ
        apply (b λ).orthonormal.2
        intro e
        exact h (by cases e; rfl)
      · exact different_eigenspaces_orthogonal J hJ h' (b λ i).property (b μ j).property
  have hSub (λ : 𝕜) : operatorEigenspace J λ ≤ Submodule.span 𝕜 (Set.range v) := by
    intro x hx
    let y : operatorEigenspace J λ := ⟨x, hx⟩
    have hy : y ∈ Submodule.span 𝕜 (Set.range (b λ)) := by
      rw [show Submodule.span 𝕜 (Set.range (b λ)) = ⊤ from (b λ).toBasis.span_eq]
      exact Submodule.mem_top
    have hmap : (Submodule.span 𝕜 (Set.range (b λ))).map (operatorEigenspace J λ).subtype ≤
        Submodule.span 𝕜 (Set.range v) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨⟨λ, i⟩, rfl⟩
    exact hmap ⟨y, hy, rfl⟩
  have hTotal : ⊤ ≤ (Submodule.span 𝕜 (Set.range v)).topologicalClosure := by
    rw [← eigenspaces_dense J hJ hK]
    exact Submodule.topologicalClosure_mono (iSup_le hSub)
  refine ⟨HilbertBasis.mk hOrtho hTotal, ?_⟩
  intro i
  have h := congrFun (HilbertBasis.coe_mk hOrtho hTotal) i
  rw [h]
  exact (b i.1 i.2).property

end
end ManuscriptAudit.Paper10FriedrichsEigenbasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsEigenbasis.different_eigenspaces_orthogonal,
      ``ManuscriptAudit.Paper10FriedrichsEigenbasis.exists_eigenbasis] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
