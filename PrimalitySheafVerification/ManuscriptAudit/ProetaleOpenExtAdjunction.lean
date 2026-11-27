import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExactFunctorExtAdjunction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtensionExact
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestriction

/-! Native Ext from the open extension of the integer sheaf computes
ordinary native cohomology on the open, in all nonnegative degrees. -/

namespace ManuscriptAudit.ProetaleOpenExtAdjunction

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open OpenProetaleExtension (extensionByZero abelianExtensionByZeroAdjunction restriction)
open ProetaleOpenExtensionExact (extensionByZero_preservesFiniteLimits extensionByZero_preservesFiniteColimits)
open ProetaleOpenRestriction (restrictionDirectImageAdjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

abbrev integers (X : Scheme.{0}) :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The exact native open adjunction computes every ordinary degree
from the actual extension by zero of the integer coefficient sheaf. -/
def openExtEquiv (F : C X) (n : ℕ) :
    Ext ((extensionByZero j A).obj (integers U)) F n ≃+ Sheaf.H ((restriction j A).obj F) n := by
  let E := extensionByZero j A
  let R := restriction j A
  letI : PreservesFiniteLimits E := extensionByZero_preservesFiniteLimits j
  letI : PreservesFiniteColimits E := extensionByZero_preservesFiniteColimits j
  letI : E.Additive := E.additive_of_preserves_binary_products
  letI : R.IsLeftAdjoint := (restrictionDirectImageAdjunction j).isLeftAdjoint
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  exact ExactFunctorDerivedAdjunction.extAdjunction (abelianExtensionByZeroAdjunction j) (integers U) F n

end
end ManuscriptAudit.ProetaleOpenExtAdjunction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleOpenExtAdjunction.openExtEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
