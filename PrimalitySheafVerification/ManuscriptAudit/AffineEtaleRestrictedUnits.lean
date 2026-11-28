import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCechRestriction
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-! Actual restriction of the coordinate-unit sheaf on the affine basis
is the identity on the coordinate rings of objects over the open. -/

namespace ManuscriptAudit.AffineEtaleRestrictedUnits

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleOpenRestriction AffineEtaleRestrictionEvaluation
open AffineEtaleCechRestriction KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private def coordinatePresheafIso :
    (affinePostcompose j).op ⋙ (coordinateUnitSheaf X).obj ≅ (coordinateUnitSheaf U).obj :=
  NatIso.ofComponents (fun D => Iso.refl _) (by
    intro D E f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id] <;> rfl)

/-- The concrete affine coordinate-unit comparison, induced by identity
on the coordinates and the natural evaluation isomorphism. -/
def restrictionUnitsIso :
    (affineRestriction j).obj (coordinateUnitSheaf X) ≅ coordinateUnitSheaf U :=
  (fullyFaithfulSheafToPresheaf (Scheme.AffineEtale.topology U) AddCommGrpCat.{0}).preimageIso
    ((restrictionPresheafIso j (coordinateUnitSheaf X)) ≪≫ coordinatePresheafIso j)

/-- Pullback of an actual unit section is literally induced by the
underlying map of affine coordinate rings. -/
theorem restrictionUnits_section {D : U.AffineEtale} {V : X.AffineEtale}
    (r : (affinePostcompose j).obj D ⟶ V) (v : Additive (V.left.unop)ˣ) :
    ((restrictionUnitsIso j).hom.hom.app (op D)).hom
        ((restrictSection j (coordinateUnitSheaf X) r).hom v) =
      Additive.ofMul (Units.map r.left.unop.hom.toMonoidHom v.toMul) := by
  let e := restrictionPresheafIso j (coordinateUnitSheaf X)
  let x := ((coordinateUnitSheaf X).obj.map r.op).hom v
  change (e.hom.app (op D)).hom ((e.inv.app (op D)).hom x) = x
  exact (e.app (op D)).addCommGroupIsoToAddEquiv.apply_symm_apply x

end

end ManuscriptAudit.AffineEtaleRestrictedUnits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleRestrictedUnits.restrictionUnitsIso,
      ``ManuscriptAudit.AffineEtaleRestrictedUnits.restrictionUnits_section] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
