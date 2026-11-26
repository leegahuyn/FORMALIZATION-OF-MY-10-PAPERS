import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Algebraic.Integral
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification

/-!
# Geometric boundary of the proper cusp compactification

The affine cusp is not proper over its field: properness of an affine
map would make the cusp algebra finite, and its finite normalization
would make the polynomial variable integral over the field.
The dense affine cusp therefore has nonempty complement in its proper
schematic closure. A residue field and its algebraic closure supply an
actual geometric point of the complement.
-/

namespace ManuscriptAudit.CuspProperBoundary

open AlgebraicGeometry CategoryTheory
open CuspPunctured CuspProperCompactification

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

/-- The actual affine cusp over a field is not proper. -/
theorem affineCusp_notProper :
    ¬ IsProper (Spec.map (CommRingCat.ofHom (algebraMap K (CuspSubalgebra K)))) := by
  intro h
  let f : CommRingCat.of K ⟶ CommRingCat.of (CuspSubalgebra K) :=
    CommRingCat.ofHom (algebraMap K (CuspSubalgebra K))
  have hFinite : IsFinite (Spec.map f) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨h, inferInstance⟩
  letI : Module.Finite K (CuspSubalgebra K) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff f).mp hFinite)
  letI : Module.Finite (CuspSubalgebra K) (Polynomial K) :=
    CuspDelta.paper2_cusp_inclusion_finite K
  letI : Module.Finite K (Polynomial K) :=
    Module.Finite.trans (R := K) (CuspSubalgebra K) (Polynomial K)
  exact Polynomial.transcendental_X K
    (IsIntegral.of_finite K (Polynomial.X : Polynomial K)).isAlgebraic

/-- The proper compactification has a point outside the image of the affine cusp. -/
theorem boundary_nonempty : (Set.range (affineOpen K))ᶜ.Nonempty := by
  classical
  by_contra h
  have hSurj : Surjective (affineOpen K) := ⟨fun x => by
    by_contra hx
    exact h ⟨x, hx⟩⟩
  haveI : IsIso (affineOpen K) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨affineOpen_isOpenImmersion K, hSurj⟩
  haveI : IsProper (projectiveCuspToBase K) := projectiveCusp_isProper K
  have hProper : IsProper (affineOpen K ≫ projectiveCuspToBase K) := inferInstance
  rw [affineOpen_toBase] at hProper
  exact affineCusp_notProper K hProper

/-- The dense affine cusp over a field is irreducible, so its closure is irreducible. -/
theorem projectiveCusp_irreducible : IrreducibleSpace (projectiveCusp K) := by
  letI : IrreducibleSpace (affineCusp K) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (CuspSubalgebra K)))
  letI : IsDominant (affineOpen K) := affineOpen_isDominant K
  have hRange : IsIrreducible (Set.range (affineOpen K)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (affineCusp K)).image _
      (affineOpen K).continuous.continuousOn
  have hClosure : closure (Set.range (affineOpen K)) = Set.univ :=
    dense_iff_closure_eq.mp (affineOpen K).denseRange
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (projectiveCusp K))
  rw [← hClosure]
  exact hRange.closure

theorem projectiveCusp_preconnected : PreconnectedSpace (projectiveCusp K) := by
  letI := projectiveCusp_irreducible K
  infer_instance

/-- An algebraically closed extension of the residue field of a point. -/
abbrev BoundaryField (x : projectiveCusp K) :=
  AlgebraicClosure ((projectiveCusp K).residueField x)

def geometricPoint (x : projectiveCusp K) :
    Spec (CommRingCat.of (BoundaryField K x)) ⟶ projectiveCusp K :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ((projectiveCusp K).residueField x) (BoundaryField K x))) ≫
      (projectiveCusp K).fromSpecResidueField x

theorem geometricPoint_apply (x : projectiveCusp K) (p : Spec (CommRingCat.of (BoundaryField K x))) :
    geometricPoint K x p = x := by
  change (projectiveCusp K).fromSpecResidueField x
    (Spec.map (CommRingCat.ofHom
      (algebraMap ((projectiveCusp K).residueField x) (BoundaryField K x))) p) = x
  exact Scheme.fromSpecResidueField_apply x _

/-- A geometric point of the proper cusp does not factor through the affine open. -/
theorem boundary_geometricPoint :
    ∃ x : projectiveCusp K,
      ¬ ∃ t : Spec (CommRingCat.of (BoundaryField K x)) ⟶ affineCusp K,
        t ≫ affineOpen K = geometricPoint K x := by
  obtain ⟨x, hx⟩ := boundary_nonempty K
  refine ⟨x, ?_⟩
  rintro ⟨t, ht⟩
  let p : Spec (CommRingCat.of (BoundaryField K x)) := (⊥ : PrimeSpectrum (BoundaryField K x))
  have he : affineOpen K (t p) = x := by
    change (t ≫ affineOpen K) p = x
    rw [ht]
    exact geometricPoint_apply K x p
  exact hx ⟨t p, he⟩

end

end ManuscriptAudit.CuspProperBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspProperBoundary.affineCusp_notProper,
      ``ManuscriptAudit.CuspProperBoundary.boundary_nonempty,
      ``ManuscriptAudit.CuspProperBoundary.projectiveCusp_irreducible,
      ``ManuscriptAudit.CuspProperBoundary.projectiveCusp_preconnected,
      ``ManuscriptAudit.CuspProperBoundary.geometricPoint_apply,
      ``ManuscriptAudit.CuspProperBoundary.boundary_geometricPoint] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
