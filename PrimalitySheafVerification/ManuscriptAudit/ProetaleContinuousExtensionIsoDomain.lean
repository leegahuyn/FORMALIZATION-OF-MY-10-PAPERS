import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtensionIsoDomain

/-! Transporting the source of the compactifying open carries its
actual native extension by zero of continuous coefficients. -/

namespace ManuscriptAudit.ProetaleContinuousExtensionIsoDomain

open AlgebraicGeometry CategoryTheory
open OpenProetaleExtension (extensionByZero)
open ProetaleOpenExtensionComposition (extensionByZeroCompIso)
open ProetaleOpenExtensionIsoDomain (extensionEquivalenceIso)
open SchemeIsoProetaleSheaves (functionsIso)
open ProetaleContinuousDirectImageMaps (functions)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}

variable {V U X : Scheme.{0}} (e : V ≅ U) (j : U ⟶ X) [IsOpenImmersion j]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

def extensionFunctionsIsoOfSourceIso :
    (extensionByZero (e.hom ≫ j) A).obj (functions M V) ≅
      (extensionByZero j A).obj (functions M U) :=
  ((extensionByZeroCompIso e.hom j).symm.app (functions M V)) ≪≫
    (extensionByZero j A).mapIso (((extensionEquivalenceIso e).app (functions M V)) ≪≫ functionsIso e M)

end

end ManuscriptAudit.ProetaleContinuousExtensionIsoDomain

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleContinuousExtensionIsoDomain.extensionFunctionsIsoOfSourceIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
