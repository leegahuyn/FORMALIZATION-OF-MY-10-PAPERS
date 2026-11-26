import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspInfinitySupport
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveBoundary

/-! The proper nodal closure adds exactly one boundary point. -/

namespace ManuscriptAudit.NodalInfinitySupport

open AlgebraicGeometry CategoryTheory
open NodalConductor NodalProjectiveClosure NodalProjectiveBoundary

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

private theorem affineNode_notProper (h2 : (2 : K) ≠ 0) :
    ¬ IsProper (Spec.map (CommRingCat.ofHom (algebraMap K (coordinates K)))) := by
  intro h
  let f : CommRingCat.of K ⟶ CommRingCat.of (coordinates K) :=
    CommRingCat.ofHom (algebraMap K (coordinates K))
  have hf : IsFinite (Spec.map f) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨h, inferInstance⟩
  letI : Module.Finite K (coordinates K) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff f).mp hf)
  letI : Module.Finite (coordinates K) (Polynomial K) :=
    NodalNormalization.normalization_finite K h2
  letI : Module.Finite K (Polynomial K) :=
    Module.Finite.trans (R := K) (coordinates K) (Polynomial K)
  exact Polynomial.transcendental_X K
    (IsIntegral.of_finite K (Polynomial.X : Polynomial K)).isAlgebraic

theorem boundary_nonempty (h2 : (2 : K) ≠ 0) :
    (Set.range (affineOpen K))ᶜ.Nonempty := by
  classical
  by_contra h
  have hSurj : Surjective (affineOpen K) := ⟨fun x => by
    by_contra hx
    exact h ⟨x, hx⟩⟩
  haveI : IsIso (affineOpen K) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨affineOpen_isOpenImmersion K, hSurj⟩
  haveI : IsProper (projectiveNodeToBase K) := projectiveNode_isProper K
  have hp : IsProper (affineOpen K ≫ projectiveNodeToBase K) := inferInstance
  rw [affineOpen_toBase] at hp
  exact affineNode_notProper K h2 hp

/-- The proper split node has exactly one point outside its affine chart. -/
theorem affine_complement_singleton (h2 : (2 : K) ≠ 0) :
    ∃ p : projectiveNode K, (Set.range (affineOpen K))ᶜ = {p} := by
  obtain ⟨p, hp⟩ := boundary_nonempty K h2
  refine ⟨p, Set.ext fun q => ?_⟩
  constructor
  · intro hq
    apply Set.mem_singleton_iff.mpr
    apply (nodeInPlane K).imageι.isClosedEmbedding.injective
    obtain ⟨hxq, hzq, hyq⟩ := boundary_plane_coordinates K q hq
    obtain ⟨hxp, hzp, hyp⟩ := boundary_plane_coordinates K p hp
    exact CuspInfinitySupport.projectivePlane_infinity_unique K _ _
      hxq hzq hyq hxp hzp hyp
  · intro hq
    rw [Set.mem_singleton_iff.mp hq]
    exact hp

theorem projectiveNode_irreducible : IrreducibleSpace (projectiveNode K) := by
  letI : IrreducibleSpace (affineNode K) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (coordinates K)))
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

end
end ManuscriptAudit.NodalInfinitySupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalInfinitySupport.boundary_nonempty,
      ``ManuscriptAudit.NodalInfinitySupport.affine_complement_singleton,
      ``ManuscriptAudit.NodalInfinitySupport.projectiveNode_irreducible] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
