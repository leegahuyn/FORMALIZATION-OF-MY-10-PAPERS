import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! A finite family of genuine principal opens is represented by the
product of the localization algebras, and its branch labels are continuous. -/

namespace ManuscriptAudit.FinitePrincipalCoverAlgebra

open AlgebraicGeometry CategoryTheory

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {I : Type} [Finite I] (r : I → R)

abbrev Local (i : I) := Localization.Away (r i)

abbrev Ring := ∀ i, Local r i

abbrev coverMap : Spec (CommRingCat.of (Ring r)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Ring r)))

abbrev branchPoint (i : I) (p : PrimeSpectrum (Local r i)) : PrimeSpectrum (Ring r) :=
  PrimeSpectrum.sigmaToPi (Local r) ⟨i, p⟩

/-- Each branch maps back by its actual localization map. -/
theorem coverMap_branch (i : I) (p : PrimeSpectrum (Local r i)) :
    coverMap r (branchPoint r i p) = PrimeSpectrum.comap (algebraMap R (Local r i)) p := by
  change PrimeSpectrum.comap (algebraMap R (Ring r))
    (PrimeSpectrum.comap (Pi.evalRingHom (Local r) i) p) = _
  rw [← PrimeSpectrum.comap_comp_apply]
  rfl

theorem from_branch (p : PrimeSpectrum (Ring r)) : ∃ i q, branchPoint r i q = p := by
  obtain ⟨⟨i, q⟩, hq⟩ := (PrimeSpectrum.sigmaToPiHomeo (Local r)).surjective p
  exact ⟨i, q, hq⟩

theorem coverMap_branch_mem (i : I) (p : PrimeSpectrum (Local r i)) :
    coverMap r (branchPoint r i p) ∈ (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)) := by
  rw [coverMap_branch, ← PrimeSpectrum.localization_away_comap_range (Local r i) (r i)]
  exact ⟨p, rfl⟩

theorem etale : Algebra.Etale R (Ring r) := by
  letI (i : I) : Algebra.Etale R (Local r i) := Algebra.Etale.of_isLocalizationAway (r i)
  exact inferInstanceAs (Algebra.Etale R (∀ i, Local r i))

theorem faithfullyFlat
    (hCover : ∀ p : PrimeSpectrum R, ∃ i, p ∈ (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R))) :
    Module.FaithfullyFlat R (Ring r) := by
  letI := etale r
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  obtain ⟨i, hi⟩ := hCover p
  rw [← PrimeSpectrum.localization_away_comap_range (Local r i) (r i)] at hi
  obtain ⟨q, hq⟩ := hi
  exact ⟨branchPoint r i q, (coverMap_branch r i q).trans hq⟩

variable {M : Type*} [TopologicalSpace M]

/-- Arbitrary constant branch labels define a genuine continuous section on the product chart. -/
def labels (c : I → M) : C(Spec (CommRingCat.of (Ring r)), M) := by
  let e := PrimeSpectrum.sigmaToPiHomeo (Local r)
  let h : Continuous (fun x : Σ i, PrimeSpectrum (Local r i) ↦ c x.1) := by
    rw [continuous_sigma_iff]
    intro i
    exact continuous_const
  exact ⟨(fun x ↦ c x.1) ∘ e.symm, h.comp e.symm.continuous⟩

theorem labels_branch (c : I → M) (i : I) (p : PrimeSpectrum (Local r i)) :
    labels r c (branchPoint r i p) = c i := by
  let e := PrimeSpectrum.sigmaToPiHomeo (Local r)
  change c (e.symm (e ⟨i, p⟩)).1 = c i
  rw [e.symm_apply_apply]

end

end ManuscriptAudit.FinitePrincipalCoverAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FinitePrincipalCoverAlgebra.coverMap_branch_mem,
      ``ManuscriptAudit.FinitePrincipalCoverAlgebra.etale,
      ``ManuscriptAudit.FinitePrincipalCoverAlgebra.faithfullyFlat,
      ``ManuscriptAudit.FinitePrincipalCoverAlgebra.labels_branch] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
