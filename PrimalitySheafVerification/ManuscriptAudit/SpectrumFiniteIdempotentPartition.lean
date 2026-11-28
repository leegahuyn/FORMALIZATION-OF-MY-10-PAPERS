import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Idempotents

/-! Finite discrete functions on an actual prime spectrum are represented
by complete orthogonal idempotents, with the original pointwise fibers. -/

namespace ManuscriptAudit.SpectrumFiniteIdempotentPartition

open PrimeSpectrum
open scoped BigOperators

noncomputable section

variable {R A : Type*} [CommRing R] [Fintype A]

/-- Each literal finite fiber is the basic open of one of a complete family of idempotents. -/
theorem exists_idempotent_fibers [TopologicalSpace A] [DiscreteTopology A]
    (f : PrimeSpectrum R → A) (hf : Continuous f) :
    ∃ e : A → R, CompleteOrthogonalIdempotents e ∧
      ∀ a, f ⁻¹' ({a} : Set A) = (basicOpen (e a) : Set (PrimeSpectrum R)) := by
  classical
  have hF (a : A) : IsClopen (f ⁻¹' ({a} : Set A)) := by
    exact ⟨(isClosed_discrete _).preimage hf, (isOpen_discrete _).preimage hf⟩
  choose e he hOpen using fun a => exists_idempotent_basicOpen_eq_of_isClopen (hF a)
  have ho : OrthogonalIdempotents e := by
    refine ⟨he, ?_⟩
    intro a b hab
    apply basicOpen_injOn_isIdempotentElem (he a |>.mul (he b)) IsIdempotentElem.zero
    rw [basicOpen_mul, basicOpen_zero]
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro x
    change x ∈ (basicOpen (e a) : Set (PrimeSpectrum R)) ∧
      x ∈ (basicOpen (e b) : Set (PrimeSpectrum R)) ↔ False
    rw [← hOpen a, ← hOpen b]
    exact iff_false_intro fun h => hab
      ((Set.mem_singleton_iff.mp h.1).symm.trans (Set.mem_singleton_iff.mp h.2))
  have hsum : (∑ a, e a) = 1 := by
    apply basicOpen_injOn_isIdempotentElem ho.isIdempotentElem_sum IsIdempotentElem.one
    rw [basicOpen_one]
    apply top_unique
    intro x _
    have hx : x ∈ (basicOpen (e (f x)) : Set (PrimeSpectrum R)) := by
      rw [← hOpen (f x)]
      exact Set.mem_singleton _
    change (∑ a, e a) ∉ x.asIdeal
    intro h
    have hm : e (f x) * (∑ a, e a) ∈ x.asIdeal := x.asIdeal.mul_mem_left _ h
    rw [ho.mul_sum_of_mem (Finset.mem_univ (f x))] at hm
    exact (show e (f x) ∉ x.asIdeal from hx) hm
  exact ⟨e, ⟨ho, hsum⟩, hOpen⟩

variable (e : A → R) (he : CompleteOrthogonalIdempotents e)

include he in
/-- Exactly one of these idempotents avoids each literal prime ideal. -/
theorem existsUnique_label (x : PrimeSpectrum R) :
    ∃! a, x ∈ (basicOpen (e a) : Set (PrimeSpectrum R)) := by
  classical
  have hex : ∃ a, e a ∉ x.asIdeal := by
    by_contra h
    push Not at h
    have hsum : (∑ a, e a) ∈ x.asIdeal := x.asIdeal.sum_mem (fun a _ => h a)
    have hComplete : (∑ a, e a) = 1 := he.complete
    rw [hComplete] at hsum
    exact x.isPrime.one_notMem hsum
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, fun b hb => ?_⟩
  by_contra hba
  have hm : e b * e a = 0 := he.toOrthogonalIdempotents.ortho hba
  have hab : x ∈ basicOpen (e b * e a) := by
    rw [basicOpen_mul]
    exact ⟨hb, ha⟩
  rw [hm, basicOpen_zero] at hab
  exact hab

def label (x : PrimeSpectrum R) : A :=
  Classical.choose (existsUnique_label e he x)

theorem label_mem (x : PrimeSpectrum R) : x ∈ basicOpen (e (label e he x)) :=
  (Classical.choose_spec (existsUnique_label e he x)).1

theorem label_eq_of_mem (x : PrimeSpectrum R) {a : A} (h : x ∈ basicOpen (e a)) :
    label e he x = a :=
  ((Classical.choose_spec (existsUnique_label e he x)).2 a h).symm

/-- The labeling function is continuous because its fibers are the actual basic opens. -/
theorem label_continuous [TopologicalSpace A] : Continuous (label e he) := by
  rw [continuous_def]
  intro s _
  have hs : label e he ⁻¹' s =
      ⋃ a : s, (basicOpen (e a.val) : Set (PrimeSpectrum R)) := by
    ext x
    constructor
    · intro hx
      apply Set.mem_iUnion.mpr
      exact ⟨⟨label e he x, hx⟩, label_mem e he x⟩
    · intro h
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp h
      exact (label_eq_of_mem e he x ha).symm ▸ a.property
  rw [hs]
  exact isOpen_iUnion fun a => (basicOpen (e a.val)).2

end
end ManuscriptAudit.SpectrumFiniteIdempotentPartition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SpectrumFiniteIdempotentPartition.exists_idempotent_fibers,
      ``ManuscriptAudit.SpectrumFiniteIdempotentPartition.existsUnique_label,
      ``ManuscriptAudit.SpectrumFiniteIdempotentPartition.label_continuous] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
