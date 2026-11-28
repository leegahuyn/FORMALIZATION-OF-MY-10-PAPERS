import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassEnergyCompletion
import PrimalitySheafVerification.ManuscriptAudit.Paper8DenseCoreFiniteRank

/-! Reduce compactness of the actual odd Maass energy inclusion to estimates on its smooth core. -/

namespace ManuscriptAudit.Paper8OddMaassCompactCriterion

open Set Paper8OddMaassHilbertCore Paper8OddMaassEnergyCompletion Paper8DenseCoreFiniteRank
open Paper8EnergyFormResolvent
open scoped Topology

noncomputable section

def oddCoreEnergyVector (f : OddSmoothCompactCore) : OddMaassEnergySpace :=
  ⟨oddCoreEnergyGraph f, oddCoreEnergyGraph.range.le_topologicalClosure ⟨f, rfl⟩⟩

theorem oddCoreEnergyVector_dense :
    Dense (Set.range oddCoreEnergyVector) := by
  have hImage : ((↑) : OddMaassEnergySpace → OddMaassGraphAmbient) '' (Set.range oddCoreEnergyVector) =
      Set.range oddCoreEnergyGraph := by
    ext x
    constructor
    · rintro ⟨y, ⟨f, rfl⟩, rfl⟩
      exact ⟨f, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨oddCoreEnergyVector f, ⟨f, rfl⟩, rfl⟩
  intro z
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, hImage]
  exact z.property

theorem oddMaassEnergyInclusion_compact_of_smooth_cell_approx
    (hApprox : ∀ ε > (0 : ℝ), ∃ K : Submodule ℂ OddMaassL2, FiniteDimensional ℂ K ∧
      ∀ f : OddSmoothCompactCore, ∃ k : K, ‖oddCoreVector f - (k : OddMaassL2)‖ ≤ ε * ‖oddCoreEnergyGraph f‖) :
    IsCompactOperator oddMaassEnergyInclusion := by
  let J := oddMaassHilbertSubmodule.subtypeL.comp oddMaassEnergyInclusion
  have hJ : IsCompactOperator J := by
    apply isCompactOperator_of_dense_core_cell_approx J oddCoreEnergyVector_dense
    intro ε hε
    obtain ⟨K, hK, hF⟩ := hApprox ε hε
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact hF f
  have hM (v : OddMaassEnergySpace) : J v ∈ oddMaassHilbertSubmodule :=
    (oddMaassEnergyInclusion v).property
  have hClosed : IsClosed (oddMaassHilbertSubmodule : Set OddMaassL2) := isClosed_closure
  have hR := hJ.codRestrict hM hClosed
  have hEq : Set.codRestrict J oddMaassHilbertSubmodule hM = (oddMaassEnergyInclusion : _ → _) := by
    funext v
    apply Subtype.ext
    rfl
  rwa [hEq] at hR

theorem oddMaassVariationalResolvent_compact_of_smooth_cell_approx
    (hApprox : ∀ ε > (0 : ℝ), ∃ K : Submodule ℂ OddMaassL2, FiniteDimensional ℂ K ∧
      ∀ f : OddSmoothCompactCore, ∃ k : K, ‖oddCoreVector f - (k : OddMaassL2)‖ ≤ ε * ‖oddCoreEnergyGraph f‖) :
    IsCompactOperator oddMaassVariationalResolvent :=
  energyFormResolvent_compact oddMaassEnergyInclusion
    (oddMaassEnergyInclusion_compact_of_smooth_cell_approx hApprox)

end
end ManuscriptAudit.Paper8OddMaassCompactCriterion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassCompactCriterion.oddMaassVariationalResolvent_compact_of_smooth_cell_approx
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
