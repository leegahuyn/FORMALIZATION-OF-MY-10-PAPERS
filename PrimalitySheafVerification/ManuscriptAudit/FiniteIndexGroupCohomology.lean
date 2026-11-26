import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.Sylow
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import PrimalitySheafVerification.ManuscriptAudit.FiniteIndexCoinducedTrace

/-!
# Finite-index detection of vanishing for group cohomology

The unit and trace of coinduction factor multiplication by the subgroup
index. Shapiro's isomorphism then shows that a subgroup on which the
cohomology vanishes annihilates the original group by its index.
-/

namespace ManuscriptAudit.FiniteIndexGroupCohomology

open CategoryTheory Rep FiniteIndexCoinducedTrace

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

private instance cohomologyFunctor_additive (n : ℕ) :
    (groupCohomology.functor k G n).Additive := by
  change (groupCohomology.cochainsFunctor k G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).Additive
  infer_instance

/-- Vanishing on the subgroup annihilates cohomology by its index. -/
theorem index_nsmul_eq_zero (S : Subgroup G) (A : Rep.{u} k G) (n : ℕ)
    (h : Subsingleton (groupCohomology (Rep.res S.subtype A) n))
    (x : groupCohomology A n) : S.index • x = 0 := by
  letI := h
  let F := groupCohomology.functor k G n
  let e := groupCohomology.coindIso (Rep.res S.subtype A) n
  have hi : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
  have hUnit : F.map (unit S A) x = 0 := by
    apply hi
    exact Subsingleton.elim _ _
  have hMap := congrArg F.map (unit_trace S A)
  rw [F.map_comp, F.map_nsmul, F.map_id] at hMap
  have hEval := congrArg (fun g : F.obj A ⟶ F.obj A ↦ g x) hMap
  change F.map (trace S A) (F.map (unit S A) x) = S.index • x at hEval
  rw [hUnit, map_zero] at hEval
  exact hEval.symm

/-- Vanishing on all Sylow subgroups implies vanishing on a finite group. -/
theorem subsingleton_of_sylow (A : Rep.{u} k G) (n : ℕ)
    (h : ∀ (p : ℕ), p.Prime → ∀ P : Sylow p G,
      Subsingleton (groupCohomology (Rep.res (P : Subgroup G).subtype A) n)) :
    Subsingleton (groupCohomology A n) := by
  have eqZero (x : groupCohomology A n) : x = 0 := by
    by_contra hx
    have ho : addOrderOf x ≠ 1 := fun hz ↦ hx (AddMonoid.addOrderOf_eq_one_iff.mp hz)
    obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd ho
    letI : Fact p.Prime := ⟨hp⟩
    let P : Sylow p G := Classical.choice inferInstance
    have hz := index_nsmul_eq_zero (P : Subgroup G) A n (h p hp P) x
    exact P.not_dvd_index (hpD.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz))
  exact ⟨fun x y ↦ (eqZero x).trans (eqZero y).symm⟩

end

end ManuscriptAudit.FiniteIndexGroupCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FiniteIndexGroupCohomology.index_nsmul_eq_zero,
      ``ManuscriptAudit.FiniteIndexGroupCohomology.subsingleton_of_sylow] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
