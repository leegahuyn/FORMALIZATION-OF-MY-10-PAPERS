import Mathlib.RingTheory.Regular.RegularSequence

/-! Audit: the Spt7 interface `ModuleDepthDimensionInterface` (copied verbatim from
`PrimalitySheafVerification/Spt7.lean`, ~line 6709) is uninhabited for every ring. -/

universe u v

open RingTheory.Sequence

structure ModuleDepthDimensionInterface (R : Type u) [CommRing R] where
  depth : (M : Type v) → [AddCommGroup M] → [Module R M] → ℕ
  dimension : (M : Type v) → [AddCommGroup M] → [Module R M] → ℕ
  IsCohenMacaulay : (M : Type v) → [AddCommGroup M] → [Module R M] → Prop
  length_le_depth_of_isWeaklyRegular :
    ∀ {M : Type v} [AddCommGroup M] [Module R M] {rs : List R},
      IsWeaklyRegular M rs → rs.length ≤ depth M
  depth_le_dimension :
    ∀ {M : Type v} [AddCommGroup M] [Module R M], depth M ≤ dimension M
  depth_eq_dimension_of_isCohenMacaulay :
    ∀ {M : Type v} [AddCommGroup M] [Module R M],
      IsCohenMacaulay M → depth M = dimension M

/-- On a subsingleton module every list is weakly regular. -/
theorem isWeaklyRegular_of_subsingleton {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M] (rs : List R) :
    IsWeaklyRegular M rs :=
  ⟨fun i _ a b _ => by
    haveI : Subsingleton (M ⧸ (Ideal.ofList (rs.take i) • ⊤ : Submodule R M)) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact Subsingleton.elim a b⟩

theorem interface_false (R : Type u) [CommRing R]
    (I : ModuleDepthDimensionInterface.{u, v} R) : False := by
  have key : ∀ n : ℕ, n ≤ I.depth PUnit.{v+1} := fun n => by
    have h := I.length_le_depth_of_isWeaklyRegular (M := PUnit.{v+1})
      (rs := List.replicate n (0 : R)) (isWeaklyRegular_of_subsingleton _ _)
    simpa using h
  exact absurd (key (I.depth PUnit.{v+1} + 1)) (by omega)
