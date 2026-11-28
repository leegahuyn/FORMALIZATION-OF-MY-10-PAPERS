import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCohomologyPresheaf
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoOpenHOne

/-! Evaluation of the native étale cohomology presheaf on the identity
object computes the actual small étale cohomology of the scheme. -/

namespace ManuscriptAudit.EtaleTerminalCohomology

open AlgebraicGeometry CategoryTheory Opposite
open OpenEtaleExtension EtaleTwoOpenHOne

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable (X : Scheme.{u})

private def postcomposeIdIso : etalePostcompose (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents
    (fun U => MorphismProperty.Over.isoMk (Iso.refl U.left) (by simp))
    (by
      intro U V f
      apply MorphismProperty.Over.Hom.ext
      change f.left ≫ 𝟙 V.left = 𝟙 U.left ≫ f.left
      simp)

private def identityRestrictionIso (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (restriction (𝟙 X) AddCommGrpCat.{u}).obj F ≅ F := by
  apply (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
  change (etalePostcompose (𝟙 X)).op ⋙ F.obj ≅ F.obj
  exact Functor.isoWhiskerRight (NatIso.op (postcomposeIdIso X)).symm F.obj ≪≫
    Functor.leftUnitor F.obj

/-- The actual terminal-object value of the native cohomology presheaf
is the true étale cohomology group in every degree. -/
def terminalHEquiv (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    F.H' n (identityObject X) ≃+ Sheaf.H F n :=
  (openCohomologyPresheafEquiv (𝟙 X) F n).trans
    (((Sheaf.functorH X.smallEtaleTopology n).mapIso (identityRestrictionIso X F)).addCommGroupIsoToAddEquiv)

end

end ManuscriptAudit.EtaleTerminalCohomology

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleTerminalCohomology.terminalHEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
