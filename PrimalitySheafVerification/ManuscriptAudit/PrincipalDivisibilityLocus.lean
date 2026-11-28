import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Divisibility at prime stalks defines an actual open locus.
Ideal membership on all stalks detects ordinary global ideal membership. -/

namespace ManuscriptAudit.PrincipalDivisibilityLocus

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The open where the class of x modulo J actually vanishes. -/
def membershipOpen (J : Ideal A) (x : A) : TopologicalSpace.Opens (PrimeSpectrum A) :=
  ⟨(PrimeSpectrum.zeroLocus ((J.colon {x} : Ideal A) : Set A))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

theorem mem_membershipOpen_iff (J : Ideal A) (x : A) (p : PrimeSpectrum A) :
    p ∈ membershipOpen J x ↔
      algebraMap A (Localization.AtPrime p.asIdeal) x ∈
        J.map (algebraMap A (Localization.AtPrime p.asIdeal)) := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.asIdeal.primeCompl]
  change ¬ (((J.colon {x} : Ideal A) : Set A) ⊆ p.asIdeal) ↔
    ∃ a ∈ p.asIdeal.primeCompl, a * x ∈ J
  constructor
  · intro h
    by_contra h'
    apply h
    intro a ha
    by_contra hmem
    apply h'
    exact ⟨a, hmem, by simpa only [smul_eq_mul] using
      (Submodule.mem_colon_singleton.mp ha)⟩
  · rintro ⟨a, ha, hx⟩ h
    apply ha
    apply h
    exact Submodule.mem_colon_singleton.mpr (by simpa only [smul_eq_mul] using hx)

/-- The actual open on which a divides x in each prime local ring. -/
abbrev divisibilityOpen (a x : A) : TopologicalSpace.Opens (PrimeSpectrum A) :=
  membershipOpen (Ideal.span ({a} : Set A)) x

theorem mem_divisibilityOpen_iff (a x : A) (p : PrimeSpectrum A) :
    p ∈ divisibilityOpen a x ↔
      algebraMap A (Localization.AtPrime p.asIdeal) a ∣
        algebraMap A (Localization.AtPrime p.asIdeal) x := by
  rw [mem_membershipOpen_iff, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]

/-- If an element belongs to an ideal in every actual prime stalk,
it already belongs to the ideal of the ring. -/
theorem mem_of_forall_local (J : Ideal A) (x : A)
    (h : ∀ p : PrimeSpectrum A, algebraMap A (Localization.AtPrime p.asIdeal) x ∈
      J.map (algebraMap A (Localization.AtPrime p.asIdeal))) : x ∈ J := by
  by_contra hx
  let S := J.colon ({x} : Set A)
  have hS : S ≠ ⊤ := by
    intro he
    apply hx
    exact (Submodule.colon_eq_top_iff_subset (N := (J : Submodule A A)) {x}).mp he
      (Set.mem_singleton x)
  obtain ⟨m, hm, hSm⟩ := Ideal.exists_le_maximal S hS
  let p : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have hp := (mem_membershipOpen_iff J x p).mpr (h p)
  exact hp hSm

/-- Divisibility in every actual prime stalk implies divisibility in the ring. -/
theorem dvd_of_forall_atPrime (a x : A)
    (h : ∀ p : PrimeSpectrum A, algebraMap A (Localization.AtPrime p.asIdeal) a ∣
      algebraMap A (Localization.AtPrime p.asIdeal) x) : a ∣ x := by
  apply Ideal.mem_span_singleton.mp
  refine mem_of_forall_local (Ideal.span ({a} : Set A)) x (fun p ↦ ?_)
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact h p

/-- Divisibility is transported by the actual localization map between
corresponding prime local rings. -/
theorem map_dvd_atPrime (f : A →+* B) (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : p = q.comap f) {a x : A}
    (h : algebraMap A (Localization.AtPrime p) a ∣ algebraMap A (Localization.AtPrime p) x) :
    algebraMap B (Localization.AtPrime q) (f a) ∣
      algebraMap B (Localization.AtPrime q) (f x) := by
  let g := Localization.localRingHom p q f hpq
  obtain ⟨z, hz⟩ := h
  refine ⟨g z, ?_⟩
  have hv := congrArg g hz
  rw [map_mul, Localization.localRingHom_to_map, Localization.localRingHom_to_map] at hv
  exact hv

end
end ManuscriptAudit.PrincipalDivisibilityLocus

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PrincipalDivisibilityLocus.mem_divisibilityOpen_iff,
      ``ManuscriptAudit.PrincipalDivisibilityLocus.dvd_of_forall_atPrime,
      ``ManuscriptAudit.PrincipalDivisibilityLocus.map_dvd_atPrime] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
