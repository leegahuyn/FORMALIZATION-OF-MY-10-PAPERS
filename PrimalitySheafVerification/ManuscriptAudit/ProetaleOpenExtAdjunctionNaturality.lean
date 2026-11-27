import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExactFunctorExtAdjunctionNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtAdjunction

/-! Changing coefficients commutes with the actual native open Ext adjunction. -/

namespace ManuscriptAudit.ProetaleOpenExtAdjunctionNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open OpenProetaleExtension (extensionByZero abelianExtensionByZeroAdjunction restriction)
open ProetaleOpenExtensionExact (extensionByZero_preservesFiniteLimits extensionByZero_preservesFiniteColimits)
open ProetaleOpenRestriction (restrictionDirectImageAdjunction)
open ProetaleOpenExtAdjunction (integers openExtEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

set_option maxHeartbeats 1600000 in
theorem naturality {F G : C X} (f : F ⟶ G) (n : ℕ)
    (x : Ext ((extensionByZero j A).obj (integers U)) F n) :
    openExtEquiv j G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      Sheaf.H.map ((restriction j A).map f) n (openExtEquiv j F n x) := by
  let E := extensionByZero j A
  let R := restriction j A
  letI : PreservesFiniteLimits E := extensionByZero_preservesFiniteLimits j
  letI : PreservesFiniteColimits E := extensionByZero_preservesFiniteColimits j
  letI : E.Additive := E.additive_of_preserves_binary_products
  letI : R.IsLeftAdjoint := (restrictionDirectImageAdjunction j).isLeftAdjoint
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : R.Additive := R.additive_of_preserves_binary_products
  exact ExactFunctorExtAdjunctionNaturality.naturality (abelianExtensionByZeroAdjunction j)
    (integers U) f n x

end
end ManuscriptAudit.ProetaleOpenExtAdjunctionNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleOpenExtAdjunctionNaturality.naturality
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
