import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHigherCohomology

/-!
# Positive étale cohomology of finite sums of skyscrapers

The actual small-étale cohomology functor preserves finite biproducts.
Each geometric skyscraper is acyclic in positive degree, so each
finite sum is also acyclic.
-/

namespace ManuscriptAudit.GeometricSkyscraperCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] etaleSiteHasExt

/-- A finite sum of actual geometric skyscrapers has zero positive
cohomology on the small étale site. -/
theorem finiteSkyscraperCoproduct_H_succ_subsingleton {X : Scheme.{u}}
    {I : Type u} [Finite I] (p : I → X.smallEtaleTopology.Point.{u})
    (M : I → AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H (∐ fun i ↦ (p i).skyscraperSheaf (M i)) (n + 1)) := by
  let S : I → Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := fun i ↦ (p i).skyscraperSheaf (M i)
  let H := Sheaf.functorH X.smallEtaleTopology (n + 1)
  letI : PreservesBiproduct S H := inferInstance
  letI : PreservesColimit (Discrete.functor S) H :=
    preservesCoproduct_of_preservesBiproduct H
  have hZero (i : I) : IsZero (H.obj (S i)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (geometricSkyscraperH_succ_subsingleton (p i) (M i) n)
  exact AddCommGrpCat.subsingleton_of_isZero (mapCoproduct_isZero H S hZero)

end

end ManuscriptAudit.GeometricSkyscraperCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.GeometricSkyscraperCohomology.finiteSkyscraperCoproduct_H_succ_subsingleton
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
