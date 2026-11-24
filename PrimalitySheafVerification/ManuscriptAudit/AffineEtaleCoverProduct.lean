import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Finite affine étale covers and faithfully flat products

Quasi-compactness selects a finite subcover of an affine étale cover.
The product of a finite covering family is an étale faithfully flat
algebra over the affine base.
-/

namespace ManuscriptAudit.AffineEtaleCoverProduct

open AlgebraicGeometry

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v} (A : ι → Type u)
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ i, Algebra.Etale R (A i)]

/-- Every jointly surjective family of affine étale maps to an affine
scheme has a finite jointly surjective subfamily. -/
theorem finite_affine_etale_subcover
    (h : ∀ x : PrimeSpectrum R, ∃ (i : ι) (y : PrimeSpectrum (A i)),
      PrimeSpectrum.comap (algebraMap R (A i)) y = x) :
    ∃ t : Finset ι, ∀ x : PrimeSpectrum R, ∃ i ∈ t, ∃ y : PrimeSpectrum (A i),
      PrimeSpectrum.comap (algebraMap R (A i)) y = x := by
  classical
  let U (i : ι) : Set (PrimeSpectrum R) :=
    Set.range (PrimeSpectrum.comap (algebraMap R (A i)))
  have hs : (Set.univ : Set (PrimeSpectrum R)) ⊆ ⋃ i, U i := by
    intro x _
    obtain ⟨i, y, hy⟩ := h x
    exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  have hopen (i : ι) : IsOpen (U i) := by
    let f := Spec.map (CommRingCat.ofHom (algebraMap R (A i)))
    letI : Etale f :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale R (A i)))
    change IsOpen (Set.range f)
    exact f.isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen hs
  refine ⟨t, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hit, y, hy⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, hit, y, hy⟩

/-- The product algebra of a finite jointly surjective affine étale
family is étale and faithfully flat over the base ring. -/
theorem product_affine_etale_faithfullyFlat [Finite ι]
    (h : ∀ x : PrimeSpectrum R, ∃ (i : ι) (y : PrimeSpectrum (A i)),
      PrimeSpectrum.comap (algebraMap R (A i)) y = x) :
    Algebra.Etale R (∀ i, A i) ∧ Module.FaithfullyFlat R (∀ i, A i) := by
  letI : Algebra.Etale R (∀ i, A i) := inferInstance
  refine ⟨inferInstance, Module.FaithfullyFlat.of_comap_surjective ?_⟩
  intro x
  obtain ⟨i, y, hy⟩ := h x
  let g := Pi.evalRingHom A i
  refine ⟨PrimeSpectrum.comap g y, ?_⟩
  have hh : PrimeSpectrum.comap (algebraMap R (∀ i, A i)) (PrimeSpectrum.comap g y) =
      PrimeSpectrum.comap (algebraMap R (A i)) y := PrimeSpectrum.ext_iff.mpr rfl
  exact hh.trans hy

end ManuscriptAudit.AffineEtaleCoverProduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleCoverProduct.finite_affine_etale_subcover,
      ``ManuscriptAudit.AffineEtaleCoverProduct.product_affine_etale_faithfullyFlat] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
