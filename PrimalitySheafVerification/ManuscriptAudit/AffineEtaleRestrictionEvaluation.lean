import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleOpenRestriction

/-! The actual restriction after transport to the affine bases is
objectwise precomposition with affine étale postcomposition. -/

namespace ManuscriptAudit.AffineEtaleRestrictionEvaluation

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleOpenRestriction OpenEtaleExtension

noncomputable section

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := AddCommGrpCat.{u}
private abbrev E (Y : Scheme.{u}) := Scheme.AffineEtale.sheafEquiv Y C.{u}

/-- The value of a restricted affine sheaf is the original value on the
same affine scheme with its composite structure morphism. -/
def restrictionPresheafIso (I : Sheaf (Scheme.AffineEtale.topology X) C.{u}) :
    ((affineRestriction j).obj I).obj ≅ (affinePostcompose j).op ⋙ I.obj := by
  let F := (E X).functor.obj I
  let A := Scheme.AffineEtale.Spec U ⋙ etalePostcompose j
  let B := affinePostcompose j ⋙ Scheme.AffineEtale.Spec X
  let f : B ≅ A := postcomposeSpecIso j
  let fOp : A.op ≅ B.op :=
    { hom := NatTrans.op f.hom
      inv := NatTrans.op f.inv
      hom_inv_id := by rw [← NatTrans.op_comp, f.inv_hom_id, NatTrans.op_id]
      inv_hom_id := by rw [← NatTrans.op_comp, f.hom_inv_id, NatTrans.op_id] }
  let e : (Scheme.AffineEtale.Spec X).op ⋙ F.obj ≅ I.obj :=
    (sheafToPresheaf (Scheme.AffineEtale.topology X) C.{u}).mapIso ((E X).unitIso.app I).symm
  change A.op ⋙ F.obj ≅ _
  exact (isoWhiskerRight fOp F.obj) ≪≫ (isoWhiskerLeft (affinePostcompose j).op e)

end

end ManuscriptAudit.AffineEtaleRestrictionEvaluation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleRestrictionEvaluation.restrictionPresheafIso
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
