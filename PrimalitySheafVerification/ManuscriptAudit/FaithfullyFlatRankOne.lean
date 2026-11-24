import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Faithfully flat rank-one descent over a PID

An actual module over a principal ideal domain is isomorphic to its base
ring if faithful flat scalar extension identifies it with a free module
of rank one. This is the module freeness step for an affine unit descent
argument.
-/

namespace ManuscriptAudit.FaithfullyFlatRankOne

open TensorProduct

/-- A module that becomes free of rank one after faithful flat scalar
extension is free of rank one over a principal ideal domain. -/
theorem rank_one_descends_over_pid (R B M : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [CommRing B] [Algebra R B] [Module.FaithfullyFlat R B]
    [AddCommGroup M] [Module R M] (e : (B ⊗[R] M) ≃ₗ[B] B) :
    Nonempty (M ≃ₗ[R] R) := by
  letI : Nontrivial B := (TensorProduct.lid R B).toEquiv.nontrivial_congr.mp inferInstance
  letI : Module.Finite B (B ⊗[R] M) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  letI : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
  letI : Module.Flat B (B ⊗[R] M) := Module.Flat.of_linearEquiv e
  letI : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M B
  letI : Module.IsTorsionFree R M := inferInstance
  let b := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := M)
  letI : Module.Free R M := Module.Free.of_basis b.2
  have hrank : Module.finrank R M = Module.finrank R R := calc
    _ = Fintype.card (Fin b.1) := Module.finrank_eq_card_basis b.2
    _ = Module.finrank B (B ⊗[R] M) := (Module.finrank_eq_card_basis (b.2.baseChange B)).symm
    _ = Module.finrank B B := e.finrank_eq
    _ = 1 := Module.finrank_self B
    _ = Module.finrank R R := (Module.finrank_self R).symm
  exact ⟨LinearEquiv.ofFinrankEq (R := R) M R hrank⟩

end ManuscriptAudit.FaithfullyFlatRankOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.FaithfullyFlatRankOne.rank_one_descends_over_pid
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
