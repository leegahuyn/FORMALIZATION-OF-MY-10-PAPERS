import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCechRestriction

/-! The actual affine site evaluation comparison commutes with sheaf maps. -/

namespace ManuscriptAudit.AffineEtaleRestrictionNaturality

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleOpenRestriction AffineEtaleRestrictionEvaluation OpenEtaleExtension
open AffineEtaleCechRestriction

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev C := AddCommGrpCat.{u}
private abbrev E := Scheme.AffineEtale.sheafEquiv X C.{u}

theorem restrictionPresheafIso_natural
    {I J : Sheaf (Scheme.AffineEtale.topology X) C.{u}} (f : I ⟶ J) (D : U.AffineEtale) :
    ((affineRestriction j).map f).hom.app (op D) ≫
      (restrictionPresheafIso j J).hom.app (op D) =
    (restrictionPresheafIso j I).hom.app (op D) ≫
      f.hom.app (op ((affinePostcompose j).obj D)) := by
  let V := (affinePostcompose j).obj D
  let e := ((postcomposeSpecIso j).hom.app D).op
  let a := ((E (X := X)).functor.map f).hom
  let A := ((E (X := X)).functor.obj I).obj
  let B := ((E (X := X)).functor.obj J).obj
  let i := ((E (X := X)).unitIso.inv.app I).hom.app (op V)
  let k := ((E (X := X)).unitIso.inv.app J).hom.app (op V)
  have ha : A.map e ≫ a.app _ = a.app _ ≫ B.map e := a.naturality e
  have hi : a.app _ ≫ k = i ≫ f.hom.app (op V) := by
    have n := (E (X := X)).unitIso.inv.naturality f
    exact congrArg (fun g : (E (X := X)).inverse.obj ((E (X := X)).functor.obj I) ⟶ J =>
      g.hom.app (op V)) n
  change a.app _ ≫ (B.map e ≫ k) = (A.map e ≫ i) ≫ f.hom.app (op V)
  rw [← Category.assoc, ← ha, Category.assoc, hi, ← Category.assoc]


/-- Pulling back a section commutes with each actual morphism of sheaves. -/
theorem restrictSection_sheafMap
    {I J : Sheaf (Scheme.AffineEtale.topology X) C.{u}} (f : I ⟶ J)
    {D : U.AffineEtale} {V : X.AffineEtale} (r : (affinePostcompose j).obj D ⟶ V) :
    f.hom.app (op V) ≫ restrictSection j J r =
      restrictSection j I r ≫ ((affineRestriction j).map f).hom.app (op D) := by
  let i := (restrictionPresheafIso j I).app (op D)
  let k := (restrictionPresheafIso j J).app (op D)
  let q := ((affineRestriction j).map f).hom.app (op D)
  let b := f.hom.app (op ((affinePostcompose j).obj D))
  have he : q ≫ k.hom = i.hom ≫ b := restrictionPresheafIso_natural j f D
  have hInv : i.inv ≫ q = b ≫ k.inv := by
    apply (cancel_mono k.hom).mp
    rw [Category.assoc, he, ← Category.assoc, i.inv_hom_id, Category.id_comp,
      Category.assoc, k.inv_hom_id, Category.comp_id]
  unfold restrictSection
  change f.hom.app (op V) ≫ J.obj.map r.op ≫ k.inv =
    (I.obj.map r.op ≫ i.inv) ≫ q
  rw [← Category.assoc, ← f.hom.naturality r.op, Category.assoc, Category.assoc, hInv]

end

end ManuscriptAudit.AffineEtaleRestrictionNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleRestrictionNaturality.restrictionPresheafIso_natural,
      ``ManuscriptAudit.AffineEtaleRestrictionNaturality.restrictSection_sheafMap] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
