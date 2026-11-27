import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHOne
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionHZero

/-! The native compact-support degree zero of the affine nodal curve vanishes. -/

namespace ManuscriptAudit.NodalCompactSupportHZero

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (affineNode affineOpen affineOpen_isDominant projectiveNode)
open NodalRationalInfinity (infinityPoint infinityPoint_outside)
open NodalCompactSupportHOne (nodalHc)

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type u) [Field K]

/-- The actual projective node is irreducible as the closure of its irreducible affine chart. -/
theorem projectiveNode_irreducible : IrreducibleSpace (projectiveNode K) := by
  letI : IrreducibleSpace (affineNode K) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (NodalConductor.coordinates K)))
  letI : IsDominant (affineOpen K) := affineOpen_isDominant K
  have hRange : IsIrreducible (Set.range (affineOpen K)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (affineNode K)).image _
      (affineOpen K).continuous.continuousOn
  have hClosure : closure (Set.range (affineOpen K)) = Set.univ :=
    dense_iff_closure_eq.mp (affineOpen K).denseRange
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (projectiveNode K))
  rw [← hClosure]
  exact hRange.closure

variable [IsSepClosed K]

/-- The actual degree-zero compact-support group is zero for any abelian constant coefficient. -/
theorem compact_HZero_subsingleton (M : AddCommGrpCat.{u}) :
    Subsingleton (nodalHc K M 0) := by
  letI : IrreducibleSpace (projectiveNode K) := projectiveNode_irreducible K
  apply OpenEtaleExtension.extensionByZeroConstantHZero_subsingleton (affineOpen K) M (infinityPoint K)
  rintro ⟨t, ht⟩
  have hx := congrArg (fun f : Spec (CommRingCat.of K) ⟶ projectiveNode K ↦
    f (IsLocalRing.closedPoint K)) ht
  exact infinityPoint_outside K ⟨t (IsLocalRing.closedPoint K), hx⟩

end
end ManuscriptAudit.NodalCompactSupportHZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCompactSupportHZero.projectiveNode_irreducible,
      ``ManuscriptAudit.NodalCompactSupportHZero.compact_HZero_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
