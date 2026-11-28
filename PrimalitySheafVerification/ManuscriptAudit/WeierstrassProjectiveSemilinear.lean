import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SchematicImageIso
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassSemilinearAffineChart

/-! The actual semilinear isomorphism of the projective Weierstrass
closure extends the literal semilinear map of its affine coordinates. -/

namespace ManuscriptAudit.WeierstrassProjectiveSemilinear

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassSemilinearAffineChart
open ProjectivePlaneSemilinear

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {K L : Type u} [Field K] [Field L]
variable (W : WeierstrassCurve.Affine K) (e : K ≃+* L)

private abbrev V := W.map e.toRingHom

/-- The semilinear map on the actual proper Weierstrass scheme. -/
def projectiveIso : projectiveScheme (V W e) ≅ projectiveScheme W :=
  SchematicImageIso.imageIso (inPlane W) (inPlane (V W e))
    (affineSchemeIso W e) (planeIso e) (inPlane_semilinear W e)

theorem projectiveIso_inPlane :
    (projectiveIso W e).hom ≫ (inPlane W).imageι =
      (inPlane (V W e)).imageι ≫ (planeIso e).hom :=
  SchematicImageIso.imageIso_imageι (inPlane W) (inPlane (V W e))
    (affineSchemeIso W e) (planeIso e) (inPlane_semilinear W e)

/-- The literal affine open inclusion commutes with that semilinear map. -/
theorem affineOpen_projectiveIso :
    affineOpen (V W e) ≫ (projectiveIso W e).hom =
      (affineSchemeIso W e).hom ≫ affineOpen W :=
  SchematicImageIso.toImage_imageIso (inPlane W) (inPlane (V W e))
    (affineSchemeIso W e) (planeIso e) (inPlane_semilinear W e)

end

end ManuscriptAudit.WeierstrassProjectiveSemilinear

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassProjectiveSemilinear.affineOpen_projectiveIso
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
