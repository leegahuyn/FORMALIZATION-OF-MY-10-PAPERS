import Lean.Util.CollectAxioms
import Mathlib.Topology.LocallyClosed
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsionOnSpecInt

/-!
# No locally closed stratification by fixed geometric torsion types

Any locally closed subset of Spec ℤ through the generic point is open.
It therefore contains closed primes with both types of geometric
p-torsion in the actual varying family with A = 1.
-/

namespace ManuscriptAudit.CubicGeometricTorsionStrata

open CubicGeometricTorsionOnSpecInt

theorem isOpen_of_generic_mem_of_isLocallyClosed
    (S : Set (PrimeSpectrum ℤ)) (hS : IsLocallyClosed S) (hη : (⊥ : PrimeSpectrum ℤ) ∈ S) :
    IsOpen S := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hS
  have hAll : Z = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have hgen : Specializes (⊥ : PrimeSpectrum ℤ) x :=
      (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
    exact (hgen.mem_open hZ.isOpen_compl hx) hη.2
  simpa only [hAll, Set.inter_univ] using hU

theorem no_fixed_torsionFiber_type_on_genericStratum
    (S : Set (PrimeSpectrum ℤ)) (hS : IsLocallyClosed S) (hη : (⊥ : PrimeSpectrum ℤ) ∈ S) :
    ¬ ∃ T : Type, ∀ (p : ℕ) (hp : p.Prime), primePoint p hp ∈ S →
      Nonempty (torsionFiber p hp ≃ T) :=
  no_fixed_torsionFiber_type_on_genericOpen ⟨S, isOpen_of_generic_mem_of_isLocallyClosed S hS hη⟩ hη

/-- Even a relatively open neighborhood of the generic point in a locally
closed stratum cannot have a single fixed geometric torsion type. -/
theorem no_fixed_torsionFiber_type_near_generic_on_stratum
    (S : Set (PrimeSpectrum ℤ)) (hS : IsLocallyClosed S) (hη : (⊥ : PrimeSpectrum ℤ) ∈ S) :
    ¬ ∃ (V : TopologicalSpace.Opens (PrimeSpectrum ℤ)) (T : Type),
      (⊥ : PrimeSpectrum ℤ) ∈ V ∧
        ∀ (p : ℕ) (hp : p.Prime), primePoint p hp ∈ S → primePoint p hp ∈ V →
          Nonempty (torsionFiber p hp ≃ T) := by
  rintro ⟨V, T, hηV, hT⟩
  let U : TopologicalSpace.Opens (PrimeSpectrum ℤ) :=
    ⟨S ∩ (V : Set (PrimeSpectrum ℤ)), (isOpen_of_generic_mem_of_isLocallyClosed S hS hη).inter V.isOpen⟩
  exact no_fixed_torsionFiber_type_on_genericOpen U ⟨hη, hηV⟩
    ⟨T, fun p hp h => hT p hp h.1 h.2⟩

/-- A locally closed cover cannot assign a fixed geometric torsion type to each piece. -/
theorem no_fixed_torsionFiber_types_on_locallyClosed_cover {ι : Type*}
    (S : ι → Set (PrimeSpectrum ℤ)) (hCover : ∃ i, (⊥ : PrimeSpectrum ℤ) ∈ S i)
    (hS : ∀ i, IsLocallyClosed (S i)) :
    ¬ ∀ i, ∃ T : Type, ∀ (p : ℕ) (hp : p.Prime), primePoint p hp ∈ S i →
      Nonempty (torsionFiber p hp ≃ T) := by
  intro hTypes
  obtain ⟨i, hi⟩ := hCover
  exact no_fixed_torsionFiber_type_on_genericStratum (S i) (hS i) hi (hTypes i)

end ManuscriptAudit.CubicGeometricTorsionStrata

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.CubicGeometricTorsionStrata.isOpen_of_generic_mem_of_isLocallyClosed,
        ``ManuscriptAudit.CubicGeometricTorsionStrata.no_fixed_torsionFiber_type_on_genericStratum,
        ``ManuscriptAudit.CubicGeometricTorsionStrata.no_fixed_torsionFiber_type_near_generic_on_stratum,
        ``ManuscriptAudit.CubicGeometricTorsionStrata.no_fixed_torsionFiber_types_on_locallyClosed_cover] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
