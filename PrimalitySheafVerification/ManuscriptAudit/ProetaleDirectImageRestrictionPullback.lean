import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleObjectRestriction

/-! Restriction along a weakly étale map commutes with direct image across its actual pullback square. -/

namespace ManuscriptAudit.ProetaleDirectImageRestrictionPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange ProetaleObjectRestriction
open OpenProetaleExtension (proetalePostcompose)

noncomputable section
universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y U V : Scheme.{u}} {f : Y ⟶ X} {j : U ⟶ X} {p : V ⟶ Y} {q : V ⟶ U}
variable [WeaklyEtale j] [WeaklyEtale p]

private theorem reindex_square (H : IsPullback p q f j) (W : U.ProEt) :
    IsPullback (pullback.fst W.hom q) (pullback.snd W.hom q ≫ p)
      (W.hom ≫ j) f :=
  ((IsPullback.of_hasPullback W.hom q).flip.paste_horiz H).flip

/-- The two operations on small pro-étale neighborhoods are compared by pullback pasting. -/
def reindexIso (H : IsPullback p q f j) :
    baseChange q ⋙ proetalePostcompose p ≅ proetalePostcompose j ⋙ baseChange f := by
  refine NatIso.ofComponents (fun W ↦ MorphismProperty.Over.isoMk (reindex_square H W).isoPullback
    (reindex_square H W).isoPullback_hom_snd) ?_
  intro W Z h
  let m := ((baseChange f).map ((proetalePostcompose j).map h)).left
  have hm₁ : m ≫ pullback.fst (Z.hom ≫ j) f = pullback.fst (W.hom ≫ j) f ≫ h.left := by
    simp only [m, baseChange, MorphismProperty.Over.pullback_map_left]
    change pullback.lift (pullback.fst (W.hom ≫ j) f ≫ h.left)
      (pullback.snd (W.hom ≫ j) f) _ ≫ pullback.fst (Z.hom ≫ j) f = _
    exact pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd (Z.hom ≫ j) f = pullback.snd (W.hom ≫ j) f := by
    simp only [m, baseChange, MorphismProperty.Over.pullback_map_left]
    change pullback.lift (pullback.fst (W.hom ≫ j) f ≫ h.left)
      (pullback.snd (W.hom ≫ j) f) _ ≫ pullback.snd (Z.hom ≫ j) f = _
    exact pullback.lift_snd _ _ _
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · change (((baseChange q).map h).left ≫ (reindex_square H Z).isoPullback.hom) ≫
        pullback.fst (Z.hom ≫ j) f =
      ((reindex_square H W).isoPullback.hom ≫ m) ≫ pullback.fst (Z.hom ≫ j) f
    simp only [Category.assoc]
    rw [(reindex_square H Z).isoPullback_hom_fst, hm₁,
      (reindex_square H W).isoPullback_hom_fst_assoc]
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  · change (((baseChange q).map h).left ≫ (reindex_square H Z).isoPullback.hom) ≫
        pullback.snd (Z.hom ≫ j) f =
      ((reindex_square H W).isoPullback.hom ≫ m) ≫ pullback.snd (Z.hom ≫ j) f
    simp only [Category.assoc]
    rw [(reindex_square H Z).isoPullback_hom_snd, hm₂,
      (reindex_square H W).isoPullback_hom_snd]
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd_assoc]

/-- The comparison preserves the first projection to the original chart. -/
theorem reindexIso_hom_fst (H : IsPullback p q f j) (W : U.ProEt) :
    ((reindexIso H).hom.app W).left ≫ pullback.fst (W.hom ≫ j) f = pullback.fst W.hom q :=
  (reindex_square H W).isoPullback_hom_fst

private abbrev A := AddCommGrpCat.{v}

/-- A natural comparison of the actual direct images and weakly étale restrictions. -/
def directImageRestrictionIso (H : IsPullback p q f j) :
    directImage f A.{v} ⋙ restriction j A.{v} ≅ restriction p A.{v} ⋙ directImage q A.{v} := by
  let F := proetalePostcompose j
  let G := baseChange f
  let F' := baseChange q
  let G' := proetalePostcompose p
  let e : F' ⋙ G' ≅ F ⋙ G := reindexIso H
  let θ : F.op ⋙ G.op ≅ F'.op ⋙ G'.op :=
    (CategoryTheory.Functor.opComp _ _).symm ≪≫ CategoryTheory.NatIso.op e ≪≫
      CategoryTheory.Functor.opComp _ _
  refine NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf (Scheme.ProEt.topology U) A.{v}).preimageIso ?_) ?_
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

set_option maxHeartbeats 4900000 in
/-- The literal component is restriction along the actual pasted comparison. -/
theorem directImageRestrictionIso_hom_app_app (H : IsPullback p q f j)
    (M : Sheaf (Scheme.ProEt.topology Y) A.{v}) (W : U.ProEt) :
    ((directImageRestrictionIso H).hom.app M).hom.app (op W) =
      M.obj.map ((reindexIso H).hom.app W).op := by
  let F := proetalePostcompose j
  let G := baseChange f
  let F' := baseChange q
  let G' := proetalePostcompose p
  let θ : F.op ⋙ G.op ≅ F'.op ⋙ G'.op :=
    (CategoryTheory.Functor.opComp _ _).symm ≪≫ CategoryTheory.NatIso.op (reindexIso H) ≪≫
      CategoryTheory.Functor.opComp _ _
  have hθ : θ.hom.app (op W) = ((reindexIso H).hom.app W).op := by
    change 𝟙 _ ≫ (((reindexIso H).hom.app W).op ≫ 𝟙 _) = _
    rw [Category.id_comp, Category.comp_id]
  change 𝟙 _ ≫ (M.obj.map (θ.hom.app (op W)) ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id, hθ]

end
end ManuscriptAudit.ProetaleDirectImageRestrictionPullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleDirectImageRestrictionPullback.reindexIso,
      ``ManuscriptAudit.ProetaleDirectImageRestrictionPullback.directImageRestrictionIso,
      ``ManuscriptAudit.ProetaleDirectImageRestrictionPullback.directImageRestrictionIso_hom_app_app] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
