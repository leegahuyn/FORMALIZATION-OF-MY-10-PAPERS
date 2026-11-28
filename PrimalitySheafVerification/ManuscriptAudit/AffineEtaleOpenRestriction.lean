import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionExact
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-! Postcomposition along an open immersion on the actual affine basis of
the small étale site, with the square relating the full and affine sites. -/

namespace ManuscriptAudit.AffineEtaleOpenRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenEtaleExtension KummerUnitsSheaf

noncomputable section

universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Compose an affine étale object over an open with its open immersion. -/
def affinePostcompose : U.AffineEtale ⥤ X.AffineEtale where
  obj V := by
    letI : Etale V.hom := V.prop
    exact Scheme.AffineEtale.mk (V.hom ≫ j)
  map f := MorphismProperty.CostructuredArrow.homMk f.left trivial (by
    change Scheme.Spec.map f.left ≫ _ ≫ j = _ ≫ j
    rw [← Category.assoc, f.w])
  map_id _ := by apply MorphismProperty.CostructuredArrow.Hom.ext; rfl
  map_comp _ _ := by apply MorphismProperty.CostructuredArrow.Hom.ext; rfl

/-- Postcomposition commutes with taking the spectrum of each affine object. -/
def postcomposeSpecIso :
    affinePostcompose j ⋙ Scheme.AffineEtale.Spec X ≅
      Scheme.AffineEtale.Spec U ⋙ etalePostcompose j :=
  NatIso.ofComponents
    (fun V => MorphismProperty.Over.isoMk (Iso.refl (Spec V.left.unop)) (by
      change 𝟙 _ ≫ (V.hom ≫ j) = V.hom ≫ j
      exact Category.id_comp _))
    (by
      intro V T f
      apply (Scheme.Etale.forget X).map_injective
      apply CostructuredArrow.hom_ext
      change Scheme.Spec.map f.left ≫ 𝟙 _ = 𝟙 _ ≫ Scheme.Spec.map f.left
      rw [Category.comp_id, Category.id_comp])

end

end ManuscriptAudit.AffineEtaleOpenRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleOpenRestriction.affinePostcompose,
      ``ManuscriptAudit.AffineEtaleOpenRestriction.postcomposeSpecIso] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
