import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Unramified.Locus

/-! Flat finitely presented stages have affine étale neighborhoods at
their unramified points, with any specified local denominators inverted. -/

namespace ManuscriptAudit.FlatUnramifiedEtaleNeighborhood

noncomputable section

universe u

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
  [Module.Flat A D] [Algebra.FinitePresentation A D]

/-- One can shrink an étale neighborhood to invert a specified
element that already avoids the point. -/
theorem exists_etale_away (q : Ideal D) [q.IsPrime] [Algebra.IsUnramifiedAt A q]
    (g : D) (hg : g ∉ q) :
    ∃ f : D, f ∉ q ∧ g ∣ f ∧ Algebra.Etale A (Localization.Away f) := by
  obtain ⟨a, ha, hu⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := A) q
  let f := a * g
  refine ⟨f, ‹q.IsPrime›.mul_notMem ha hg, ⟨a, mul_comm a g⟩, ?_⟩
  have hq : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
      Algebra.unramifiedLocus A D :=
    (PrimeSpectrum.basicOpen_mul_le_left a g).trans
      (Algebra.basicOpen_subset_unramifiedLocus_iff.mpr hu)
  letI : Algebra.FormallyUnramified A (Localization.Away f) :=
    Algebra.basicOpen_subset_unramifiedLocus_iff.mp hq
  exact Algebra.Etale.of_formallyUnramified_of_flat

end
end ManuscriptAudit.FlatUnramifiedEtaleNeighborhood

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FlatUnramifiedEtaleNeighborhood.exists_etale_away
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
