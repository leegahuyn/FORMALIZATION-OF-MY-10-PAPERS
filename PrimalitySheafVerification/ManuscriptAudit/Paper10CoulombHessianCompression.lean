import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombPartition

/-! A bounded scalar Hessian can leave the Coulomb slice; its projection has the expected bound. -/

namespace ManuscriptAudit.Paper10CoulombHessianCompression

open Paper10CoulombMultiplier Paper10CoulombProductRule Paper10CoulombPartition
open scoped ContDiff RealInnerProductSpace

noncomputable section

/-- There is a smooth bounded real multiplier on the width-two cusp cylinder,
supported in a bounded height band, whose multiplication leaves the Coulomb slice. -/
theorem smooth_bounded_multiplier_leaves_slice :
    ∃ v : ScalarField, ContDiff ℝ ∞ v.uncurry ∧
      (∀ x y, v x y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ (x y : ℝ) (m : ℤ), v (x + 2 * (m : ℝ)) y = v x y) ∧
      (∀ x y, y ≤ 2 ∨ 4 ≤ y → v x y = 0) ∧
      (∀ x y, codifferential witnessForm x y = 0) ∧
      codifferential (scaleOneForm v witnessForm) 0 3 ≠ 0 := by
  refine ⟨first, partition_smooth.1, ?_, fun x y m => (partition_periodic x y m).1,
    first_zero_off_height_band, partition_pieces_not_coulomb.1, ?_⟩
  · intro x y
    obtain ⟨h₀, h₁, hEq⟩ := partition_properties x y
    exact ⟨h₀, by linarith⟩
  · rw [partition_pieces_not_coulomb.2.1]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by norm_num))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S : Submodule ℝ H) [S.HasOrthogonalProjection]

/-- The bounded perturbation associated to the restricted quadratic form. -/
def compress (V : H →L[ℝ] H) : S →L[ℝ] S :=
  S.orthogonalProjectionOnto ∘L (V ∘L S.subtypeL)

theorem compress_inner (V : H →L[ℝ] H) (x y : S) :
    ⟪compress S V x, y⟫ = ⟪V (x : H), (y : H)⟫ :=
  S.inner_orthogonalProjectionOnto_eq_of_mem_right y (V (x : H))

theorem compress_norm_le (V : H →L[ℝ] H) :
    ‖compress S V‖ ≤ ‖V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V)
  intro x
  exact (S.norm_orthogonalProjectionOnto_apply_le (V (x : H))).trans (V.le_opNorm (x : H))

theorem compress_selfAdjoint [CompleteSpace H] [CompleteSpace S]
    (V : H →L[ℝ] H) (hV : IsSelfAdjoint V) :
    IsSelfAdjoint (compress S V) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hV ⊢
  intro x y
  change ⟪compress S V x, y⟫ = ⟪x, compress S V y⟫
  rw [compress_inner]
  exact (hV (x : H) (y : H)).trans
    (S.inner_orthogonalProjectionOnto_eq_of_mem_left x (V (y : H))).symm

theorem compress_agrees_iff (V : H →L[ℝ] H) (x : S) :
    ((compress S V x : S) : H) = V (x : H) ↔ V (x : H) ∈ S := by
  constructor
  · intro h
    rw [← h]
    exact (compress S V x).property
  · intro h
    have hi := S.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨V (x : H), h⟩ : S)
    exact congrArg Subtype.val hi

end
end ManuscriptAudit.Paper10CoulombHessianCompression

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10CoulombHessianCompression.smooth_bounded_multiplier_leaves_slice,
      ``ManuscriptAudit.Paper10CoulombHessianCompression.compress_inner,
      ``ManuscriptAudit.Paper10CoulombHessianCompression.compress_norm_le,
      ``ManuscriptAudit.Paper10CoulombHessianCompression.compress_selfAdjoint,
      ``ManuscriptAudit.Paper10CoulombHessianCompression.compress_agrees_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
