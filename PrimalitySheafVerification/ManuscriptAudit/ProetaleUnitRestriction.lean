import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitSheaf

/-! Restriction of genuine pro-étale regular-function units to an open
is the genuine pro-étale units sheaf of the open. -/

namespace ManuscriptAudit.ProetaleUnitRestriction

open AlgebraicGeometry CategoryTheory
open ProetaleUnitSheaf OpenProetaleExtension

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual units restriction, read directly on the same underlying schemes. -/
def restrictionUnitsIso :
    (restriction j AddCommGrpCat.{1}).obj (unitSheaf X) ≅ unitSheaf U :=
  (sheafToPresheaf (Scheme.ProEt.topology U) AddCommGrpCat.{1}).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro A B f
      rw [Category.comp_id, Category.id_comp] <;> rfl))

end
end ManuscriptAudit.ProetaleUnitRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleUnitRestriction.restrictionUnitsIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
