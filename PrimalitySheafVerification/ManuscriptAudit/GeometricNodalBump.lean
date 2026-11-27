import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Dimension.Finrank
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOneExact
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothCharts

/-! Over an algebraically closed field of odd characteristic, the actual
proper node has zero ordinary mod-two étale bump despite nonsmoothness. -/

namespace ManuscriptAudit.GeometricNodalBump

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure NodalProjectiveHOneExact

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev M := ZMod 2
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev smoothHOne :=
  Sheaf.H ((constantSheaf (NodalSmoothLocusOverlap.smoothScheme K).smallEtaleTopology
    AddCommGrpCat.{0}).obj (AddCommGrpCat.of M)) 1

private def coefficientModule {V : Type*} [AddCommGroup V] (e : M ≃+ V) : Module M V :=
  AddCommGroup.zmodModule fun x => by
    obtain ⟨a, rfl⟩ := e.surjective x
    have hCast : ((2 : ℕ) : M) = 0 := by decide
    have ha : (2 : ℕ) • a = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (R := M), hCast, zero_smul]
    rw [← map_nsmul, ha, map_zero]

def properModule (h2 : (2 : K) ≠ 0) : Module M (projectiveHOne K) :=
  coefficientModule (projectiveHOneEquiv K h2).symm

def smoothModule (h2 : (2 : K) ≠ 0) : Module M (smoothHOne K) :=
  coefficientModule ((projectiveHOneEquiv K h2).symm.trans (properSmoothHOneEquiv K h2))

set_option maxRecDepth 7000 in
set_option maxHeartbeats 650000 in
/-- Both actual ordinary degree-one dimensions are one. -/
theorem finranks (h2 : (2 : K) ≠ 0) :
    letI := properModule K h2
    letI := smoothModule K h2
    Module.finrank M (projectiveHOne K) = 1 ∧ Module.finrank M (smoothHOne K) = 1 := by
  letI := properModule K h2
  letI := smoothModule K h2
  let e : M ≃+ projectiveHOne K := (projectiveHOneEquiv K h2).symm
  let f : M ≃+ smoothHOne K := e.trans (properSmoothHOneEquiv K h2)
  let eL : M ≃ₗ[M] projectiveHOne K := { e with map_smul' := ZMod.map_smul e }
  let fL : M ≃ₗ[M] smoothHOne K := { f with map_smul' := ZMod.map_smul f }
  exact ⟨eL.finrank_eq.symm.trans (CommSemiring.finrank_self _),
    fL.finrank_eq.symm.trans (CommSemiring.finrank_self _)⟩

/-- The geometric ordinary bump can vanish on a genuine nonsmooth curve. -/
theorem zero_bump_and_not_smooth (h2 : (2 : K) ≠ 0) :
    letI := properModule K h2
    letI := smoothModule K h2
    ((Module.finrank M (projectiveHOne K) : ℤ) - Module.finrank M (smoothHOne K) = 0) ∧
      ¬ AlgebraicGeometry.Smooth (projectiveNodeToBase K) := by
  letI := properModule K h2
  letI := smoothModule K h2
  obtain ⟨hp, hs⟩ := finranks K h2
  exact ⟨by rw [hp, hs, sub_self], NodalSmoothCharts.projectiveNode_not_smooth K⟩

end
end ManuscriptAudit.GeometricNodalBump

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GeometricNodalBump.finranks,
      ``ManuscriptAudit.GeometricNodalBump.zero_bump_and_not_smooth] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
