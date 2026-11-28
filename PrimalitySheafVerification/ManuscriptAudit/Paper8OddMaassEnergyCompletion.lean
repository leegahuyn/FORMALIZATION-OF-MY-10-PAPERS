import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.ProdL2
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassCovariantGradient
import PrimalitySheafVerification.ManuscriptAudit.Paper8EnergyFormResolvent

/-! The actual covariant graph closure and its dense variational inclusion on level four. -/

namespace ManuscriptAudit.Paper8OddMaassEnergyCompletion

open Set MeasureTheory
open Paper8OddMaassHilbertCore Paper8OddMaassCovariantGradient Paper8EnergyFormResolvent
open scoped ENNReal

noncomputable section

def oddCoreIntoHilbert : OddSmoothCompactCore →ₗ[ℂ] OddMaassHilbertSpace :=
  oddCoreLinear.codRestrict oddMaassHilbertSubmodule (fun f =>
    oddCoreLinear.range.le_topologicalClosure ⟨f, rfl⟩)

abbrev OddMaassCovariantPair := WithLp 2 (OddMaassL2 × OddMaassL2)

abbrev OddMaassGraphAmbient := WithLp 2 (OddMaassHilbertSpace × OddMaassCovariantPair)

def oddCoreCovariantPair : OddSmoothCompactCore →ₗ[ℂ] OddMaassCovariantPair :=
  (WithLp.linearEquiv 2 ℂ (OddMaassL2 × OddMaassL2)).symm.toLinearMap.comp
    (oddCovariantXL2.prod oddCovariantYL2)

def oddCoreEnergyGraph : OddSmoothCompactCore →ₗ[ℂ] OddMaassGraphAmbient :=
  (WithLp.linearEquiv 2 ℂ (OddMaassHilbertSpace × OddMaassCovariantPair)).symm.toLinearMap.comp
    (oddCoreIntoHilbert.prod oddCoreCovariantPair)

def oddMaassEnergySubmodule : Submodule ℂ OddMaassGraphAmbient :=
  oddCoreEnergyGraph.range.topologicalClosure

abbrev OddMaassEnergySpace := ↥oddMaassEnergySubmodule

instance : CompleteSpace OddMaassEnergySpace := by
  have hClosed : IsClosed (oddMaassEnergySubmodule : Set OddMaassGraphAmbient) := isClosed_closure
  exact hClosed.completeSpace_coe

def oddMaassEnergyInclusion : OddMaassEnergySpace →L[ℂ] OddMaassHilbertSpace :=
  (WithLp.fstL (p := 2) (𝕜 := ℂ) (α := OddMaassHilbertSpace) (β := OddMaassCovariantPair)).comp
    oddMaassEnergySubmodule.subtypeL

private theorem oddCoreIntoHilbert_range_dense :
    Dense (Set.range oddCoreIntoHilbert) := by
  have hImage : ((↑) : OddMaassHilbertSpace → OddMaassL2) '' (Set.range oddCoreIntoHilbert) =
      Set.range oddCoreLinear := by
    ext x
    constructor
    · rintro ⟨y, ⟨f, rfl⟩, rfl⟩
      exact ⟨f, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨oddCoreIntoHilbert f, ⟨f, rfl⟩, rfl⟩
  intro y
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, hImage]
  exact y.property

theorem oddMaassEnergyInclusion_dense :
    oddMaassEnergyInclusion.range.topologicalClosure = ⊤ := by
  have hSubset : Set.range oddCoreIntoHilbert ⊆ (oddMaassEnergyInclusion.range : Set OddMaassHilbertSpace) := by
    rintro _ ⟨f, rfl⟩
    let u : OddMaassEnergySpace :=
      ⟨oddCoreEnergyGraph f, oddCoreEnergyGraph.range.le_topologicalClosure ⟨f, rfl⟩⟩
    exact ⟨u, rfl⟩
  apply top_unique
  intro u _
  exact closure_mono hSubset (oddCoreIntoHilbert_range_dense u)

def oddMaassVariationalResolvent : OddMaassHilbertSpace →L[ℂ] OddMaassHilbertSpace :=
  energyFormResolvent oddMaassEnergyInclusion

theorem oddMaassVariationalResolvent_symmetric : oddMaassVariationalResolvent.IsSymmetric :=
  energyFormResolvent_symmetric oddMaassEnergyInclusion

theorem oddMaassVariationalResolvent_injective : Function.Injective oddMaassVariationalResolvent :=
  energyFormResolvent_injective oddMaassEnergyInclusion oddMaassEnergyInclusion_dense

end
end ManuscriptAudit.Paper8OddMaassEnergyCompletion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddMaassEnergyCompletion.oddMaassEnergyInclusion_dense,
      ``ManuscriptAudit.Paper8OddMaassEnergyCompletion.oddMaassVariationalResolvent_injective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
