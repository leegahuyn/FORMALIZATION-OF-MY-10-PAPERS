import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension
import PrimalitySheafVerification.ManuscriptAudit.ProetaleInverseImage

/-! Restriction to an open on the actual small pro-étale site has both
adjoints and carries constant sheaves to constant sheaves. -/

namespace ManuscriptAudit.ProetaleOpenRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OpenProetaleExtension
open ProetaleBaseChange (baseChange directImage)

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

abbrev G := AddCommGrpCat.{u + 1}

/-- Restriction to an open is left adjoint to the actual direct image. -/
def restrictionDirectImageAdjunction :
    restriction j G.{u} ⊣ directImage j G.{u} := by
  letI := postcomposeContinuous j
  let a : proetalePostcompose j ⊣ baseChange j :=
    MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (show WeaklyEtale j from inferInstance) trivial
  exact a.sheafPushforwardContinuous (E := G.{u}) (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- Actual open restriction carries a constant pro-étale sheaf to the same constant sheaf. -/
def restrictionConstantIso :
    constantSheaf (Scheme.ProEt.topology X) G.{u} ⋙ restriction j G.{u} ≅
      constantSheaf (Scheme.ProEt.topology U) G.{u} := by
  let aX := constantSheafAdj (Scheme.ProEt.topology X) G.{u} (terminalIsTerminal (C := X.ProEt))
  let aU := constantSheafAdj (Scheme.ProEt.topology U) G.{u}
    (isLimitOfHasTerminalOfPreservesLimit (baseChange j))
  exact (aX.comp (restrictionDirectImageAdjunction j)).leftAdjointUniq aU

end
end ManuscriptAudit.ProetaleOpenRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenRestriction.restrictionDirectImageAdjunction,
      ``ManuscriptAudit.ProetaleOpenRestriction.restrictionConstantIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
