import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction

/-! Restriction along an étale map commutes with direct image across its actual pullback square. -/

namespace ManuscriptAudit.EtaleDirectImageRestrictionPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleObjectRestriction

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y U V : Scheme.{u}} {f : Y ⟶ X} {j : U ⟶ X} {p : V ⟶ Y} {q : V ⟶ U}
variable [Etale j] [Etale p]

private theorem reindex_square (H : IsPullback p q f j) (W : U.Etale) :
    IsPullback (pullback.fst W.hom q) (pullback.snd W.hom q ≫ p)
      (W.hom ≫ j) f :=
  ((IsPullback.of_hasPullback W.hom q).flip.paste_horiz H).flip

/-- The two operations on small-étale neighborhoods are compared by pullback pasting. -/
def reindexIso (H : IsPullback p q f j) :
    etaleBaseChange q ⋙ postcompose p ≅ postcompose j ⋙ etaleBaseChange f := by
  refine NatIso.ofComponents (fun W ↦ MorphismProperty.Over.isoMk (reindex_square H W).isoPullback
    (reindex_square H W).isoPullback_hom_snd) ?_
  intro W Z h
  let m := ((etaleBaseChange f).map ((postcompose j).map h)).left
  have hm₁ : m ≫ pullback.fst (Z.hom ≫ j) f = pullback.fst (W.hom ≫ j) f ≫ h.left := by
    simp only [m, etaleBaseChange, MorphismProperty.Over.pullback_map_left]
    change pullback.lift (pullback.fst (W.hom ≫ j) f ≫ h.left)
      (pullback.snd (W.hom ≫ j) f) _ ≫ pullback.fst (Z.hom ≫ j) f = _
    exact pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd (Z.hom ≫ j) f = pullback.snd (W.hom ≫ j) f := by
    simp only [m, etaleBaseChange, MorphismProperty.Over.pullback_map_left]
    change pullback.lift (pullback.fst (W.hom ≫ j) f ≫ h.left)
      (pullback.snd (W.hom ≫ j) f) _ ≫ pullback.snd (Z.hom ≫ j) f = _
    exact pullback.lift_snd _ _ _
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change (((etaleBaseChange q).map h).left ≫ (reindex_square H Z).isoPullback.hom) ≫
        pullback.fst (Z.hom ≫ j) f =
      ((reindex_square H W).isoPullback.hom ≫ m) ≫ pullback.fst (Z.hom ≫ j) f
    simp only [Category.assoc]
    rw [(reindex_square H Z).isoPullback_hom_fst, hm₁,
      (reindex_square H W).isoPullback_hom_fst_assoc]
    simp only [etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  · change (((etaleBaseChange q).map h).left ≫ (reindex_square H Z).isoPullback.hom) ≫
        pullback.snd (Z.hom ≫ j) f =
      ((reindex_square H W).isoPullback.hom ≫ m) ≫ pullback.snd (Z.hom ≫ j) f
    simp only [Category.assoc]
    rw [(reindex_square H Z).isoPullback_hom_snd, hm₂,
      (reindex_square H W).isoPullback_hom_snd]
    simp only [etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd_assoc]

private abbrev A := AddCommGrpCat.{u}

/-- A natural comparison of the actual direct images and étale restrictions. -/
def directImageRestrictionIso (H : IsPullback p q f j) :
    directImage f A.{u} ⋙ restriction j ≅ restriction p ⋙ directImage q A.{u} := by
  let F := postcompose j
  let G := etaleBaseChange f
  let F' := etaleBaseChange q
  let G' := postcompose p
  let e : F' ⋙ G' ≅ F ⋙ G := reindexIso H
  let θ : F.op ⋙ G.op ≅ F'.op ⋙ G'.op :=
    (CategoryTheory.Functor.opComp _ _).symm ≪≫ CategoryTheory.NatIso.op e ≪≫
      CategoryTheory.Functor.opComp _ _
  refine NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf U.smallEtaleTopology A.{u}).preimageIso ?_) ?_
  · change F.op ⋙ (G.op ⋙ M.obj) ≅ F'.op ⋙ (G'.op ⋙ M.obj)
    exact (CategoryTheory.Functor.associator _ _ _).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight θ M.obj ≪≫ CategoryTheory.Functor.associator _ _ _
  · intro M N g
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext D
    change g.hom.app ((F.op ⋙ G.op).obj D) ≫ N.obj.map (θ.hom.app D) =
      M.obj.map (θ.hom.app D) ≫ g.hom.app ((F'.op ⋙ G'.op).obj D)
    exact (g.hom.naturality (θ.hom.app D)).symm

end
end ManuscriptAudit.EtaleDirectImageRestrictionPullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleDirectImageRestrictionPullback.reindexIso,
      ``ManuscriptAudit.EtaleDirectImageRestrictionPullback.directImageRestrictionIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
