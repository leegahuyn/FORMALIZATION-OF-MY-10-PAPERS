import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleDirectImageRestrictionPullback
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitSections
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionExact

/-! Restriction to a factoring open commutes with the actual regular-unit
map into the generic-point direct image. -/

namespace ManuscriptAudit.OpenEtaleGenericUnitComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleObjectRestriction EtaleDirectImageRestrictionPullback
open GenericEtaleUnitSections KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Y U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (g : Y ⟶ U)

private theorem factoringPullback : IsPullback (𝟙 Y) g (g ≫ j) j :=
  IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩

private def identityPostcomposeIso (T : Scheme.{0}) : postcompose (𝟙 T) ≅ 𝟭 T.Etale :=
  NatIso.ofComponents
    (fun V => MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp))
    (by
      intro V W f
      apply MorphismProperty.Over.Hom.ext
      change f.left ≫ 𝟙 W.left = 𝟙 V.left ≫ f.left
      simp)

private def factoringComparison : etaleBaseChange g ≅ postcompose j ⋙ etaleBaseChange (g ≫ j) :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (etaleBaseChange g) (identityPostcomposeIso Y).symm ≪≫
    reindexIso (factoringPullback j g)

private theorem factoringComparison_fst (W : U.Etale) :
    ((factoringComparison j g).hom.app W).left ≫
      pullback.fst (W.hom ≫ j) (g ≫ j) = pullback.fst W.hom g := by
  let P := ((IsPullback.of_hasPullback W.hom g).flip.paste_horiz (factoringPullback j g)).flip
  have hp : P.isoPullback.hom ≫ pullback.fst (W.hom ≫ j) (g ≫ j) = pullback.fst W.hom g :=
    P.isoPullback_hom_fst
  change ((𝟙 _ ≫ 𝟙 _) ≫ P.isoPullback.hom) ≫ pullback.fst (W.hom ≫ j) (g ≫ j) = _
  simpa only [Category.id_comp] using hp

private abbrev R := OpenEtaleExtension.restriction j AddCommGrpCat.{0}
private abbrev M := fullCoordinateUnitSheaf Y

/-- Under restriction along a factoring open, the actual generic unit
direct image agrees with the direct image of the factored point. -/
def genericUnitsIso :
    (R j).obj ((directImage (g ≫ j) AddCommGrpCat.{0}).obj (M (Y := Y))) ≅
      (directImage g AddCommGrpCat.{0}).obj (M (Y := Y)) := by
  let G := etaleBaseChange (g ≫ j)
  let H := etaleBaseChange g
  let e : H ≅ postcompose j ⋙ G := factoringComparison j g
  apply (fullyFaithfulSheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{0}).preimageIso
  change (postcompose j).op ⋙ (G.op ⋙ (M (Y := Y)).obj) ≅ H.op ⋙ (M (Y := Y)).obj
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.opComp _ _).symm ≪≫ NatIso.op e) (M (Y := Y)).obj

/-- The actual restriction of the regular-to-generic unit morphism
agrees with the true morphism for the factored generic point. -/
theorem genericUnitsSquare :
    (R j).map (pullbackToDirectImage (g ≫ j)) ≫ (genericUnitsIso j g).hom =
      (EtaleObjectRestriction.restrictionUnitsIso j).hom ≫ pullbackToDirectImage g := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  let V := unop W
  let H := Scheme.Γ ⋙ ringUnits
  change H.map (pullback.fst (V.hom ≫ j) (g ≫ j)).op ≫
    H.map (((factoringComparison j g).hom.app V).left).op =
    𝟙 _ ≫ H.map (pullback.fst V.hom g).op
  rw [Category.id_comp, ← Functor.map_comp, ← op_comp, factoringComparison_fst]

end

end ManuscriptAudit.OpenEtaleGenericUnitComparison

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleGenericUnitComparison.genericUnitsSquare
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
