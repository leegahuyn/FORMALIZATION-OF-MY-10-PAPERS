import Lean
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

open CategoryTheory Opposite TopologicalSpace

namespace ManuscriptAudit

private abbrev spectrumOfIntegers := TopCat.of (PrimeSpectrum ℤ)

private abbrev constantNaturalPresheaf :
    TopCat.Presheaf Type spectrumOfIntegers :=
  (Functor.const _).obj ℕ

/-- Paper 3, p. 54. The literal constant presheaf with value ℕ on every
open of Spec ℤ fails uniqueness of gluing for the empty family. -/
theorem paper3_constant_natural_presheaf_is_not_a_sheaf :
    ¬ constantNaturalPresheaf.IsSheaf := by
  intro h
  let opens : Empty → Opens spectrumOfIntegers := fun i => nomatch i
  let sections (i : Empty) : constantNaturalPresheaf.obj (op (opens i)) := nomatch i
  obtain ⟨gluing, _, hUnique⟩ :=
    h.isSheafUniqueGluing_types (U := opens) sections (fun i => nomatch i)
  have hZero : (0 : ℕ) = gluing := hUnique (0 : ℕ) (fun i => nomatch i)
  have hOne : (1 : ℕ) = gluing := hUnique (1 : ℕ) (fun i => nomatch i)
  exact zero_ne_one (hZero.trans hOne.symm)

end ManuscriptAudit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.paper3_constant_natural_presheaf_is_not_a_sheaf
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
