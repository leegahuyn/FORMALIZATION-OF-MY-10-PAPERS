import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtension
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension

/-! Actual change of sites commutes with extension by zero along an open immersion. -/

namespace ManuscriptAudit.EtaleProetaleOpenComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EtaleProetaleInverseImage

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{u+1}

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restricting étale objects after postcomposition agrees with postcomposing pro-étale objects. -/
def directImageRestrictionIso :
    directImage X ⋙ OpenEtaleExtension.restriction j A.{u} ≅
      OpenProetaleExtension.restriction j A.{u} ⋙ directImage U := by
  let P := sheafToPresheaf U.smallEtaleTopology A.{u}
  refine NatIso.ofComponents (fun F => P.preimageIso (Iso.refl _)) ?_
  intro F G f
  apply P.map_injective
  ext W
  rfl

/-- The left-adjoint mate gives the actual extension by zero comparison. -/
def inverseImageExtensionIso :
    OpenEtaleExtension.extensionByZero j A.{u} ⋙ inverseImage X ≅
      inverseImage U ⋙ OpenProetaleExtension.extensionByZero j A.{u} := by
  let a := (OpenEtaleExtension.extensionByZeroAdjunction j A.{u}).comp (adjunction X)
  let b := (adjunction U).comp (OpenProetaleExtension.extensionByZeroAdjunction j A.{u})
  exact (a.ofNatIsoRight (directImageRestrictionIso j)).leftAdjointUniq b

end
end ManuscriptAudit.EtaleProetaleOpenComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleOpenComparison.directImageRestrictionIso,
      ``ManuscriptAudit.EtaleProetaleOpenComparison.inverseImageExtensionIso] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
