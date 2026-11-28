import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The compact self-adjoint spectral theorem expressed directly as eigenspace cross coefficients. -/

namespace ManuscriptAudit.Paper8CompactCrossDecomposition

open Module.End
open scoped ENNReal InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem compact_eigenspace_closed (T : H →L[ℂ] H) (μ : ℂ) :
    IsClosed ((eigenspace T.toLinearMap μ) : Set H) := by
  have hS : ((eigenspace T.toLinearMap μ) : Set H) = {x : H | T x = μ • x} := by
    ext x
    exact mem_eigenspace_iff
  rw [hS]
  exact isClosed_eq T.continuous (continuous_const.smul continuous_id)

def compactCrossDecomposition (T : H →L[ℂ] H)
    (hT : IsCompactOperator T) (hSymm : T.IsSymmetric) :
    H ≃ₗᵢ[ℂ] lp (fun μ : Eigenvalues T.toLinearMap => eigenspace T.toLinearMap (μ : ℂ)) 2 := by
  letI (μ : Eigenvalues T.toLinearMap) : CompleteSpace (eigenspace T.toLinearMap (μ : ℂ)) :=
    (compact_eigenspace_closed T μ).completeSpace_coe
  have hOrth : (⨆ μ : Eigenvalues T.toLinearMap, eigenspace T.toLinearMap (μ : ℂ))ᗮ = ⊥ := by
    change (⨆ μ : {μ : ℂ // eigenspace T.toLinearMap μ ≠ ⊥}, eigenspace T.toLinearMap (μ : ℂ))ᗮ = ⊥
    rw [iSup_ne_bot_subtype]
    exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hSymm
  have hDense : (⨆ μ : Eigenvalues T.toLinearMap,
      eigenspace T.toLinearMap (μ : ℂ)).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr hOrth
  exact (IsHilbertSum.mkInternal (fun μ : Eigenvalues T.toLinearMap => eigenspace T.toLinearMap (μ : ℂ))
    hSymm.orthogonalFamily_eigenspaces' hDense.ge).linearIsometryEquiv

def compactCrossCoefficient (T : H →L[ℂ] H) (hT : IsCompactOperator T) (hSymm : T.IsSymmetric)
    (x y : H) (μ : Eigenvalues T.toLinearMap) : ℂ :=
  ⟪compactCrossDecomposition T hT hSymm x μ, compactCrossDecomposition T hT hSymm y μ⟫_ℂ

theorem hasSum_compactCrossCoefficient (T : H →L[ℂ] H) (hT : IsCompactOperator T) (hSymm : T.IsSymmetric)
    (x y : H) :
    HasSum (compactCrossCoefficient T hT hSymm x y) ⟪x, y⟫_ℂ := by
  let e := compactCrossDecomposition T hT hSymm
  have h := lp.hasSum_inner (𝕜 := ℂ) (e x) (e y)
  rw [e.inner_map_map] at h
  exact h

theorem summable_norm_compactCrossCoefficient (T : H →L[ℂ] H) (hT : IsCompactOperator T)
    (hSymm : T.IsSymmetric) (x y : H) :
    Summable (fun μ => ‖compactCrossCoefficient T hT hSymm x y μ‖) := by
  let e := compactCrossDecomposition T hT hSymm
  have hp : ((2 : ℝ≥0∞).toReal).HolderConjugate ((2 : ℝ≥0∞).toReal) := by
    simpa using Real.HolderConjugate.two_two
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun μ => ?_)
    (lp.summable_mul hp (e x) (e y))
  exact norm_inner_le_norm (𝕜 := ℂ) _ _

theorem exists_nonzero_compactCrossCoefficient (T : H →L[ℂ] H) (hT : IsCompactOperator T)
    (hSymm : T.IsSymmetric) {x y : H} (hXY : ⟪x, y⟫_ℂ ≠ 0) :
    ∃ μ, compactCrossCoefficient T hT hSymm x y μ ≠ 0 := by
  by_contra! hZero
  apply hXY
  rw [← (hasSum_compactCrossCoefficient T hT hSymm x y).tsum_eq]
  simp only [hZero, tsum_zero]

end
end ManuscriptAudit.Paper8CompactCrossDecomposition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8CompactCrossDecomposition.compactCrossDecomposition,
      ``ManuscriptAudit.Paper8CompactCrossDecomposition.exists_nonzero_compactCrossCoefficient] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
