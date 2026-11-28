import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! Finite-dimensional approximation of a dense core implies genuine compactness of the inclusion. -/

namespace ManuscriptAudit.Paper8DenseCoreFiniteRank

open Set
open scoped Topology

noncomputable section

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isCompactOperator_of_dense_core_cell_approx
    (J : V →L[ℂ] H) {D : Set V} (hD : Dense D)
    (hApprox : ∀ ε > (0 : ℝ), ∃ K : Submodule ℂ H, FiniteDimensional ℂ K ∧
      ∀ v ∈ D, ∃ k : K, ‖J v - (k : H)‖ ≤ ε * ‖v‖) :
    IsCompactOperator J := by
  let C : Set (V →L[ℂ] H) := {A | IsCompactOperator A}
  have hClosed : IsClosed C := isClosed_setOf_isCompactOperator
  have hClosure : J ∈ closure C := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨K, hK, hApp⟩ := hApprox (ε / 2) (half_pos hε)
    letI : FiniteDimensional ℂ K := hK
    let B := K.starProjection.comp J
    have hB : IsCompactOperator B :=
      (isCompactOperator_of_locallyCompactSpace_dom (K.orthogonalProjectionOnto.comp J)).clm_comp K.subtypeL
    let S : Set V := {v | ‖J v - B v‖ ≤ (ε / 2) * ‖v‖}
    have hS : IsClosed S := isClosed_le ((J.continuous.sub B.continuous).norm)
      (continuous_const.mul continuous_norm)
    have hDS : D ⊆ S := by
      intro v hv
      obtain ⟨k, hk⟩ := hApp v hv
      change ‖J v - K.starProjection (J v)‖ ≤ (ε / 2) * ‖v‖
      rw [Submodule.starProjection_minimal]
      have hb : BddBelow (Set.range fun x : K => ‖J v - (x : H)‖) :=
        ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
      exact (ciInf_le hb k).trans hk
    have hAll (v : V) : ‖(J - B) v‖ ≤ (ε / 2) * ‖v‖ :=
      closure_minimal hDS hS (hD v)
    have hNorm : ‖J - B‖ ≤ ε / 2 :=
      ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le hAll
    refine ⟨B, hB, ?_⟩
    have hDis : dist J B < ε := by
      rw [dist_eq_norm]
      exact hNorm.trans_lt (by linarith)
    simpa only [dist_comm] using hDis
  change J ∈ C
  rwa [hClosed.closure_eq] at hClosure

end
end ManuscriptAudit.Paper8DenseCoreFiniteRank

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DenseCoreFiniteRank.isCompactOperator_of_dense_core_cell_approx
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
