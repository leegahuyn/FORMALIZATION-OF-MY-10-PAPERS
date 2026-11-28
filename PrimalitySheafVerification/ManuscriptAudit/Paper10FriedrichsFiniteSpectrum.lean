import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsEigenbasis
import PrimalitySheafVerification.ManuscriptAudit.CompactOrthonormalSpectrum

/-! Counted with their genuine finite-dimensional multiplicity, only
finitely many eigenvalues of the shifted realization lie in a bounded set. -/

namespace ManuscriptAudit.Paper10FriedrichsFiniteSpectrum

open Paper10FriedrichsResolvent Paper10FriedrichsCompact Paper10FriedrichsEigenbasis

noncomputable section

variable {𝕜 D H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

variable (J : D →L[𝕜] H)

/-- The compact-resolvent eigenbasis has finitely many entries of bounded energy. -/
theorem finite_bounded_basis_indices (hJ : DenseRange J) (hK : IsCompactOperator J)
    (b : HilbertBasis (EigenIndex J) 𝕜 H)
    (hb : ∀ i, (b i, i.1 • b i) ∈ (realization J).graph)
    (R : ℝ) (hR : 0 < R) :
    Finite {i : EigenIndex J // ‖i.1‖ ≤ R} := by
  have hμ (i : EigenIndex J) : i.1 ≠ 0 := by
    intro h
    have hi := (realization_graph_iff J hJ (b i) (i.1 • b i)).mp (hb i)
    rw [h, zero_smul, map_zero] at hi
    have hnorm := b.orthonormal.1 i
    rw [← hi, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hEigen (i : EigenIndex J) : (resolvent J) (b i) = i.1⁻¹ • b i :=
    (eigenvector_reciprocity J hJ i.1 (hμ i) (b i)).mp (hb i)
  letI := CompactOrthonormalSpectrum.finite_large_labels (resolvent J) (compact_resolvent J hK)
    (fun i => b i) b.orthonormal (fun i : EigenIndex J => i.1⁻¹) hEigen
    (1 / R) (one_div_pos.mpr hR)
  let f : {i : EigenIndex J // ‖i.1‖ ≤ R} → {i : EigenIndex J // 1 / R ≤ ‖i.1⁻¹‖} :=
    fun i => ⟨i.val, by
      rw [norm_inv, ← one_div]
      exact one_div_le_one_div_of_le (norm_pos_iff.mpr (hμ i.val)) i.property⟩
  exact Finite.of_injective f (fun i j h => Subtype.ext
    (congrArg (fun c : {i : EigenIndex J // 1 / R ≤ ‖i.1⁻¹‖} => c.val) h))

end
end ManuscriptAudit.Paper10FriedrichsFiniteSpectrum

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10FriedrichsFiniteSpectrum.finite_bounded_basis_indices
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
