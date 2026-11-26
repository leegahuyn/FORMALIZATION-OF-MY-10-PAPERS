import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import PrimalitySheafVerification.ManuscriptAudit.ClosedPointCoproduct
import PrimalitySheafVerification.ManuscriptAudit.SkyscraperHOne

/-!
# First cohomology of finite sums of skyscrapers

The additive cohomology functor preserves finite biproducts. Each
skyscraper has zero first cohomology, so Paper 6's finite-stage sums do too.
-/

namespace ManuscriptAudit.FiniteSkyscraperSumHOne

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.SkyscraperHOne
open ManuscriptAudit.ClosedPointSupportDetection

noncomputable section

set_option synthInstance.maxHeartbeats 12000

private abbrev G := AddCommGrpCat.{0}

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

local instance sheaf_hasCoproduct {X : TopCat.{0}} {ι : Type} (S : ι → AbelianSheaf X) :
    HasCoproduct S := abelianSheaf_hasDiscreteColimit X (Discrete.functor S)

/-- Every finite coproduct of flasque abelian sheaves has zero native H¹. -/
theorem finiteCoproduct_H1_subsingleton {X : TopCat.{0}} {ι : Type} [Finite ι]
    (S : ι → AbelianSheaf X) (hS : ∀ i, TopCat.Sheaf.IsFlasque (S i)) :
    Subsingleton ((∐ S).H 1) := by
  let H := Sheaf.functorH (Opens.grothendieckTopology X) 1
  letI : PreservesBiproduct S H := inferInstance
  letI : PreservesColimit (Discrete.functor S) H :=
    preservesCoproduct_of_preservesBiproduct H
  have hZero (i : ι) : IsZero (H.obj (S i)) := by
    letI := hS i
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr (flasque_H1_subsingleton (S i))
  exact AddCommGrpCat.subsingleton_of_isZero (mapCoproduct_isZero H S hZero)

/-- The actual skyscraper sheaf with an arbitrary abelian coefficient. -/
def pointSummand {X : TopCat.{0}} (p : X) (A : G) : AbelianSheaf X := by
  classical
  exact skyscraperSheaf p A

theorem pointSummand_isFlasque {X : TopCat.{0}} (p : X) (A : G) :
    TopCat.Sheaf.IsFlasque (pointSummand p A) := by
  classical
  exact isFlasque_skyscraperSheaf_of_hasZeroObject p A

/-- The finite-stage skyscraper sums in Paper 6 have zero native H¹. -/
theorem finiteSkyscraperCoproduct_H1_subsingleton {X : TopCat.{0}} {ι : Type} [Finite ι]
    (p : ι → X) (A : ι → G) : Subsingleton ((∐ fun i => pointSummand (p i) (A i)).H 1) :=
  finiteCoproduct_H1_subsingleton _ (fun i => pointSummand_isFlasque (p i) (A i))

end

end ManuscriptAudit.FiniteSkyscraperSumHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FiniteSkyscraperSumHOne.finiteCoproduct_H1_subsingleton,
      ``ManuscriptAudit.FiniteSkyscraperSumHOne.finiteSkyscraperCoproduct_H1_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
