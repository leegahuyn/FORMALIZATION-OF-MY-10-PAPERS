import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction

/-! The actual direct image restricts along an open through which the
source morphism factors. -/

namespace ManuscriptAudit.OpenEtaleGenericImageRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleObjectRestriction SmallEtaleBaseChange

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable (g : Y ⟶ U)

private def postcomposeFullyFaithful : (postcompose j).FullyFaithful where
  preimage {A B} f := MorphismProperty.Over.homMk f.left (by
    have h : f.left ≫ (B.hom ≫ j) = A.hom ≫ j := MorphismProperty.Over.w f
    apply (cancel_mono j).mp
    exact (Category.assoc _ _ _).trans h)
  map_preimage f := MorphismProperty.Over.Hom.ext rfl
  preimage_map f := MorphismProperty.Over.Hom.ext rfl

/-- Postcomposition on the open followed by base change along a
factoring arrow is exactly base change to that arrow. -/
def postcomposeBaseChangeIso :
    postcompose j ⋙ etaleBaseChange (g ≫ j) ≅ etaleBaseChange g := by
  let a : postcompose j ⊣ etaleBaseChange j :=
    MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j (show Etale j from inferInstance) trivial
  letI : (postcompose j).Full := (postcomposeFullyFaithful j).full
  letI : (postcompose j).Faithful := (postcomposeFullyFaithful j).faithful
  letI : ∀ W : U.Etale, IsIso (a.unit.app W) := fun _ ↦ inferInstance
  letI : IsIso a.unit := NatIso.isIso_of_isIso_app a.unit
  let e : (𝟭 U.Etale) ≅ postcompose j ⋙ etaleBaseChange j := asIso a.unit
  let c : etaleBaseChange (g ≫ j) ≅ etaleBaseChange j ⋙ etaleBaseChange g :=
    MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g j
  exact CategoryTheory.Functor.isoWhiskerLeft (postcompose j) c ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight e.symm (etaleBaseChange g) ≪≫
    CategoryTheory.Functor.leftUnitor _

/-- Actual small-étale restriction of direct image agrees with direct
image along the factorization into the open. -/
def restrictionDirectImageIso
    (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (restriction j).obj ((directImage (g ≫ j) AddCommGrpCat.{u}).obj M) ≅
      (directImage g AddCommGrpCat.{u}).obj M := by
  let F := postcompose j
  let G := etaleBaseChange (g ≫ j)
  let H := etaleBaseChange g
  let e : F ⋙ G ≅ H := postcomposeBaseChangeIso j g
  apply (fullyFaithfulSheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
  change F.op ⋙ (G.op ⋙ M.obj) ≅ H.op ⋙ M.obj
  exact (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      ((CategoryTheory.Functor.opComp _ _).symm ≪≫ (CategoryTheory.NatIso.op e).symm) M.obj

end

end ManuscriptAudit.OpenEtaleGenericImageRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleGenericImageRestriction.postcomposeBaseChangeIso,
      ``ManuscriptAudit.OpenEtaleGenericImageRestriction.restrictionDirectImageIso] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
