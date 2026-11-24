import Lean.Util.CollectAxioms
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Finite profiles on the principal-open basis of the integer spectrum

A profile assigns a natural-number weight to the non-generic prime places
of an open, with finite nonzero support. Refinement drops the places that
leave the open. Quasi-compactness of the actual principal opens makes
gluing work for arbitrary open covers.
-/

namespace ManuscriptAudit.PrincipalOpenFiniteProfiles

open TopologicalSpace

abbrev IntSpectrum := PrimeSpectrum ℤ

/-- The non-generic prime points in the specified open. -/
abbrev PrimePlaces (U : Opens IntSpectrum) :=
  {x : IntSpectrum // x ∈ U ∧ x.asIdeal ≠ ⊥}

/-- Finitely supported weights at the non-generic prime points of an open. -/
abbrev Profile (U : Opens IntSpectrum) :=
  {a : PrimePlaces U → ℕ // {x | a x ≠ 0}.Finite}

private def incl {V U : Opens IntSpectrum} (h : V ≤ U) : PrimePlaces V ↪ PrimePlaces U where
  toFun x := ⟨x.val, h x.property.1, x.property.2⟩
  inj' := fun _ _ heq => Subtype.ext (congrArg Subtype.val heq)

/-- A profile restricts by retaining the weights of prime places in the smaller open. -/
def restrict {V U : Opens IntSpectrum} (h : V ≤ U) (s : Profile U) : Profile V :=
  ⟨fun x => s.val (incl h x), s.property.preimage_embedding (incl h)⟩

theorem restrict_self (U : Opens IntSpectrum) (s : Profile U) :
    restrict (le_refl U) s = s := by
  apply Subtype.ext
  funext x
  change s.val (incl (le_refl U) x) = s.val x
  exact congrArg s.val (Subtype.ext rfl)

theorem restrict_comp {W V U : Opens IntSpectrum} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : Profile U) : restrict h₁ (restrict h₂ s) = restrict (h₁.trans h₂) s := by
  apply Subtype.ext
  funext x
  change s.val (incl h₂ (incl h₁ x)) = s.val (incl (h₁.trans h₂) x)
  exact congrArg s.val (Subtype.ext rfl)

/-- Compatible finite profiles on an arbitrary open cover of a true principal
open `D(a)` of `Spec ℤ` glue uniquely on that principal open. -/
theorem glue_principalOpen (a : ℤ) {ι : Type*} (V : ι → Opens IntSpectrum)
    (hVU : ∀ i, V i ≤ PrimeSpectrum.basicOpen a)
    (hCover : (PrimeSpectrum.basicOpen a : Set IntSpectrum) ⊆ ⋃ i, (V i : Set IntSpectrum))
    (s : ∀ i, Profile (V i))
    (hCompatible : ∀ i j (x : IntSpectrum) (hi : x ∈ V i) (hj : x ∈ V j)
      (hp : x.asIdeal ≠ ⊥), (s i).val ⟨x, hi, hp⟩ = (s j).val ⟨x, hj, hp⟩) :
    ∃! t : Profile (PrimeSpectrum.basicOpen a), ∀ i, restrict (hVU i) t = s i := by
  classical
  let U := PrimeSpectrum.basicOpen a
  obtain ⟨F, hF⟩ := (PrimeSpectrum.isCompact_basicOpen a).elim_finite_subcover
    (fun i => (V i : Set IntSpectrum)) (fun i => (V i).isOpen) hCover
  let I := {i : ι // i ∈ F}
  have hFind (x : PrimePlaces U) : ∃ i : I, x.val ∈ V i.val := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hF x.property.1)
    obtain ⟨hFi, hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, hFi⟩, hx⟩
  let idx (x : PrimePlaces U) : I := Classical.choose (hFind x)
  have hIdx (x : PrimePlaces U) : x.val ∈ V (idx x).val :=
    Classical.choose_spec (hFind x)
  let value (x : PrimePlaces U) : ℕ := (s (idx x).val).val ⟨x.val, hIdx x, x.property.2⟩
  let supports (i : I) : Set (PrimePlaces U) :=
    incl (hVU i.val) '' {x | (s i.val).val x ≠ 0}
  have hFin : (⋃ i : I, supports i).Finite :=
    Set.finite_iUnion fun i => (s i.val).property.image _
  have hValue : {x | value x ≠ 0}.Finite := by
    apply hFin.subset
    intro x hx
    refine Set.mem_iUnion.mpr ⟨idx x, ?_⟩
    exact ⟨⟨x.val, hIdx x, x.property.2⟩, hx, Subtype.ext rfl⟩
  let t : Profile U := ⟨value, hValue⟩
  refine ⟨t, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    funext x
    let y := incl (hVU i) x
    change (s (idx y).val).val ⟨y.val, hIdx y, y.property.2⟩ = (s i).val x
    exact hCompatible (idx y).val i x.val (hIdx y) x.property.1 x.property.2
  · intro t' ht'
    apply Subtype.ext
    funext x
    let i := (idx x).val
    let y : PrimePlaces (V i) := ⟨x.val, hIdx x, x.property.2⟩
    have h := congrArg (fun p : Profile (V i) => p.val y) (ht' i)
    change t'.val (incl (hVU i) y) = t.val x at h
    have hxy : incl (hVU i) y = x := Subtype.ext rfl
    simpa only [hxy] using h

end ManuscriptAudit.PrincipalOpenFiniteProfiles

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PrincipalOpenFiniteProfiles.restrict_self,
      ``ManuscriptAudit.PrincipalOpenFiniteProfiles.restrict_comp,
      ``ManuscriptAudit.PrincipalOpenFiniteProfiles.glue_principalOpen] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
