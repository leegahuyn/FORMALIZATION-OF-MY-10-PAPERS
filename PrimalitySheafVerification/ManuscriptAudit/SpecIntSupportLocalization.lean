import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.SpecIntSupportReduction

/-!
# The support index under localization and completion at 2

Paper 6, physical p. 201, Proposition 7.2(2). The closed support
`{(3)}` has exact-support detection index zero on `Spec ℤ`.
Its actual inverse image in either `Spec ℤ_(2)` or `Spec ℤ₂` is
empty, since 3 is a unit in both rings. The index of the inverse
image is infinity in both cases.
-/

namespace ManuscriptAudit.SpecIntSupportLocalization

open CategoryTheory CategoryTheory.Abelian
open ClosedSupportDetection ExactSupportDetection SpecIntSupportReduction

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

local instance (S : TopCat.{0}) : HasExt.{0} (AbelianSheaf S) :=
  IsGrothendieckAbelian.hasExt _

/-- The closed prime `(2)` in the integer spectrum. -/
def primeTwo : PrimeSpectrum ℤ :=
  PrimeSpectrum.comap (Int.castRingHom (ZMod 2)) ⊥

theorem primeTwo_asIdeal : primeTwo.asIdeal = Ideal.span ({(2 : ℤ)} : Set ℤ) := by
  ext a
  change ((a : ℤ) : ZMod 2) ∈ (⊥ : Ideal (ZMod 2)) ↔
    a ∈ Ideal.span ({(2 : ℤ)} : Set ℤ)
  rw [Ideal.mem_bot, Ideal.mem_span_singleton]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd a 2

abbrev LocalAtTwo := Localization.AtPrime primeTwo.asIdeal

abbrev localizationMap : ℤ →+* LocalAtTwo := algebraMap ℤ LocalAtTwo

abbrev completionMap : ℤ →+* ℤ_[2] := Int.castRingHom _

theorem three_isUnit_at_two : IsUnit (localizationMap 3) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff LocalAtTwo primeTwo.asIdeal 3).2
  change (3 : ℤ) ∉ primeTwo.asIdeal
  rw [primeTwo_asIdeal, Ideal.mem_span_singleton]
  norm_num

theorem three_isUnit_in_padicTwo : IsUnit (completionMap 3) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h
  have hk : ((3 : ℤ) : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [PadicInt.ker_toZMod]
    exact h
  have hz : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) ((3 : ℤ) : ℤ_[2]) = 0 :=
    RingHom.mem_ker.mp hk
  rw [map_intCast] at hz
  exact (by decide : ((3 : ℤ) : ZMod 2) ≠ 0) hz

private theorem inverseImage_primeThree_of_isUnit {R : Type*} [CommRing R]
    (f : ℤ →+* R) (h : IsUnit (f 3)) :
    (PrimeSpectrum.comap f) ⁻¹' ({primeThree} : Set (PrimeSpectrum ℤ)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he : PrimeSpectrum.comap f x = primeThree := Set.mem_singleton_iff.mp hx
  have hMem : f 3 ∈ x.asIdeal := by
    change (3 : ℤ) ∈ (PrimeSpectrum.comap f x).asIdeal
    rw [he]
    exact three_mem_primeThree
  exact x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem hMem h)

theorem inverseImage_localizationAtTwo_primeThree :
    (PrimeSpectrum.comap localizationMap) ⁻¹' ({primeThree} : Set (PrimeSpectrum ℤ)) = ∅ :=
  inverseImage_primeThree_of_isUnit localizationMap three_isUnit_at_two

theorem inverseImage_completionAtTwo_primeThree :
    (PrimeSpectrum.comap completionMap) ⁻¹' ({primeThree} : Set (PrimeSpectrum ℤ)) = ∅ :=
  inverseImage_primeThree_of_isUnit completionMap three_isUnit_in_padicTwo

private theorem index_primeThree :
    exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) {primeThree} = 0 := by
  exact exactDetectionIndex_eq_zero_of_nonempty_closed
    (X := TopCat.of (PrimeSpectrum ℤ)) (P := {primeThree})
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal primeThree).2
      (IsPrime.to_maximal_ideal primeThree_ne_generic))
    (Set.singleton_nonempty primeThree)

theorem paper6_proposition7_2_localization_refuted :
    exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) {primeThree} ≠
      exactDetectionIndex (TopCat.of (PrimeSpectrum LocalAtTwo))
        ((PrimeSpectrum.comap localizationMap) ⁻¹' {primeThree}) := by
  rw [index_primeThree, inverseImage_localizationAtTwo_primeThree, exactDetectionIndex_empty]
  simp

theorem paper6_proposition7_2_completion_refuted :
    exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) {primeThree} ≠
      exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ_[2]))
        ((PrimeSpectrum.comap completionMap) ⁻¹' {primeThree}) := by
  rw [index_primeThree, inverseImage_completionAtTwo_primeThree, exactDetectionIndex_empty]
  simp

/-- The localization image consists of the generizations of `(2)`. -/
theorem localizationAtTwo_range :
    Set.range (PrimeSpectrum.comap localizationMap) =
      {x | x.asIdeal ≤ primeTwo.asIdeal} := by
  rw [PrimeSpectrum.localization_comap_range LocalAtTwo primeTwo.asIdeal.primeCompl]
  ext x
  change Disjoint (primeTwo.asIdeal.primeCompl : Set ℤ) (x.asIdeal : Set ℤ) ↔
    x.asIdeal ≤ primeTwo.asIdeal
  constructor
  · intro hd a ha
    by_contra hNot
    exact Set.disjoint_left.mp hd hNot ha
  · intro h
    exact Set.disjoint_left.mpr fun _ ha hb => ha (h hb)

/-- The printed principal open `D(2)` omits `(2)`, which lies in the actual image. -/
theorem localizationAtTwo_range_ne_basicOpen :
    Set.range (PrimeSpectrum.comap localizationMap) ≠
      (PrimeSpectrum.basicOpen (2 : ℤ) : Set (PrimeSpectrum ℤ)) := by
  intro h
  have hp : primeTwo ∈ Set.range (PrimeSpectrum.comap localizationMap) := by
    rw [localizationAtTwo_range]
    change primeTwo.asIdeal ≤ primeTwo.asIdeal
    exact le_rfl
  rw [h] at hp
  have hTwo : (2 : ℤ) ∈ primeTwo.asIdeal := by
    rw [primeTwo_asIdeal]
    exact Ideal.subset_span (by simp)
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hp hTwo

/-- The printed intersection with `D(2)` retains the support `(3)`. -/
theorem printed_basicOpen_intersection :
    ({primeThree} : Set (PrimeSpectrum ℤ)) ∩ (PrimeSpectrum.basicOpen (2 : ℤ) : Set _) =
      {primeThree} := by
  apply Set.inter_eq_left.mpr
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact (PrimeSpectrum.mem_basicOpen _ _).2 two_not_mem_primeThree

end

end ManuscriptAudit.SpecIntSupportLocalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpecIntSupportLocalization.primeTwo_asIdeal,
      ``ManuscriptAudit.SpecIntSupportLocalization.three_isUnit_at_two,
      ``ManuscriptAudit.SpecIntSupportLocalization.three_isUnit_in_padicTwo,
      ``ManuscriptAudit.SpecIntSupportLocalization.inverseImage_localizationAtTwo_primeThree,
      ``ManuscriptAudit.SpecIntSupportLocalization.inverseImage_completionAtTwo_primeThree,
      ``ManuscriptAudit.SpecIntSupportLocalization.paper6_proposition7_2_localization_refuted,
      ``ManuscriptAudit.SpecIntSupportLocalization.paper6_proposition7_2_completion_refuted,
      ``ManuscriptAudit.SpecIntSupportLocalization.localizationAtTwo_range,
      ``ManuscriptAudit.SpecIntSupportLocalization.localizationAtTwo_range_ne_basicOpen,
      ``ManuscriptAudit.SpecIntSupportLocalization.printed_basicOpen_intersection] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
