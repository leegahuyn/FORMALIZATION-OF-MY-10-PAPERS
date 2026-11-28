import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import PrimalitySheafVerification.ManuscriptAudit.CompactSeparatedFamily

/-! Nonzero labels of any orthonormal eigenfamily of a compact operator
have finite multiplicity outside every neighborhood of zero. -/

namespace ManuscriptAudit.CompactOrthonormalSpectrum

open scoped InnerProductSpace

noncomputable section

variable {𝕜 H I : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Compactness bounds the total number of normalized eigenvectors whose
eigenvalues have norm at least the specified positive threshold. -/
theorem finite_large_labels (T : H →L[𝕜] H) (hT : IsCompactOperator T)
    (v : I → H) (hOrtho : Orthonormal 𝕜 v) (value : I → 𝕜)
    (hEigen : ∀ i, T (v i) = value i • v i) (ε : ℝ) (hε : 0 < ε) :
    Finite {i : I // ε ≤ ‖value i‖} := by
  obtain ⟨K, hK, hImage⟩ :=
    IsCompactOperator.image_closedBall_subset_compact (f := T.toLinearMap) hT 1
  let w (i : {i : I // ε ≤ ‖value i‖}) := T (v i.val)
  have hmem (i : {i : I // ε ≤ ‖value i‖}) : w i ∈ K := by
    apply hImage
    refine ⟨v i.val, ?_, rfl⟩
    exact Metric.mem_closedBall.mpr (by rw [dist_zero_right, hOrtho.1])
  apply CompactSeparatedFamily.finite_index w K hK hmem ε hε
  intro i j hij
  have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hInner : ⟪w i, w j⟫_𝕜 = 0 := by
    change ⟪T (v i.val), T (v j.val)⟫_𝕜 = 0
    simp only [hEigen, inner_smul_left, inner_smul_right, hOrtho.2 hij', mul_zero]
  have hNi : ‖w i‖ = ‖value i.val‖ := by
    change ‖T (v i.val)‖ = _
    rw [hEigen, norm_smul, hOrtho.1, mul_one]
  apply (sq_le_sq₀ hε.le dist_nonneg).mp
  rw [dist_eq_norm, norm_sub_sq (𝕜 := 𝕜), hInner, map_zero, mul_zero, sub_zero]
  have hi : ε ≤ ‖w i‖ := hNi.symm ▸ i.property
  exact ((sq_le_sq₀ hε.le (norm_nonneg _)).mpr hi).trans
    (le_add_of_nonneg_right (sq_nonneg _))

end
end ManuscriptAudit.CompactOrthonormalSpectrum

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CompactOrthonormalSpectrum.finite_large_labels
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
