import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous sections on the arithmetic base

Continuous functions from the underlying space of `Spec ℤ` to any
Hausdorff space are constant. Thus restriction along any nonempty
scheme over `Spec ℤ` is injective on such sections.
-/

namespace ManuscriptAudit.SpecIntContinuousSections

open AlgebraicGeometry

abbrev arithBase : Scheme.{0} := Spec (CommRingCat.of ℤ)

theorem values_equal {B : Type*} [TopologicalSpace B] [T2Space B]
    (f : C(arithBase, B)) (x y : arithBase) : f x = f y := by
  letI : IrreducibleSpace arithBase := inferInstanceAs (IrreducibleSpace (PrimeSpectrum ℤ))
  have h : IsPreirreducible (Set.range f) := by
    rw [← Set.image_univ]
    exact PreirreducibleSpace.isPreirreducible_univ.image f f.continuous.continuousOn
  exact h.subsingleton ⟨x, rfl⟩ ⟨y, rfl⟩

theorem eq_const {B : Type*} [TopologicalSpace B] [T2Space B]
    (f : C(arithBase, B)) (x : arithBase) :
    f = ContinuousMap.const _ (f x) :=
  ContinuousMap.ext (fun y => values_equal f y x)

theorem comp_injective {B D : Type*} [TopologicalSpace B] [T2Space B] [TopologicalSpace D]
    (r : C(D, arithBase)) (x : D) :
    Function.Injective (fun f : C(arithBase, B) => f.comp r) := by
  intro f g h
  apply ContinuousMap.ext
  intro y
  calc
    f y = f (r x) := values_equal f y (r x)
    _ = g (r x) := congrArg (fun k : C(D, B) => k x) h
    _ = g y := values_equal g (r x) y

end ManuscriptAudit.SpecIntContinuousSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpecIntContinuousSections.values_equal,
      ``ManuscriptAudit.SpecIntContinuousSections.eq_const,
      ``ManuscriptAudit.SpecIntContinuousSections.comp_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
