import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDirectImageHOneEmbedding
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericImageRestriction
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleHOneByRepresentatives

/-! Actual direct-image H¹ on an affine open is controlled by H¹ on
the affine source whenever the map factors through that open. -/

namespace ManuscriptAudit.AffineOpenDirectImageHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open SmallEtaleBaseChange OpenEtaleGenericImageRestriction OpenEtaleHOneByRepresentatives

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {R S : CommRingCat.{u}} {X : Scheme.{u}}
variable (g : Spec S ⟶ Spec R) (j : Spec R ⟶ X) [IsOpenImmersion j]
variable (M : Sheaf (Spec S).smallEtaleTopology AddCommGrpCat.{u})

/-- If the source has vanishing H¹, so does evaluation of the actual
direct-image cohomology presheaf on the affine open. -/
theorem HOne_subsingleton (h : Subsingleton (Sheaf.H M 1)) :
    Subsingleton (((directImage (g ≫ j) AddCommGrpCat.{u}).obj M).H' 1 (Scheme.Etale.mk j)) := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
  letI : IsGrothendieckAbelian.{u} C :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{u} (C := C)
  let F := (directImage (g ≫ j) AddCommGrpCat.{u}).obj M
  let e := degreeOneEquiv j (Injective.ι F)
  let k := ((Sheaf.functorH (Spec R).smallEtaleTopology 1).mapIso
    (restrictionDirectImageIso j g M)).addCommGroupIsoToAddEquiv
  obtain ⟨q, hq⟩ := AffineEtaleDirectImageHOneEmbedding.HOne_embedding R S g M
  exact ⟨fun x y => e.injective (k.injective (hq (h.allEq (q (k (e x))) (q (k (e y))))))⟩

end

end ManuscriptAudit.AffineOpenDirectImageHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineOpenDirectImageHOne.HOne_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
