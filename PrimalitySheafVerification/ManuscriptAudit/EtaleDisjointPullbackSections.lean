import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleDisjointSections

/-! A disjoint monomorphic étale cover gives a section product on every direct-image chart. -/

namespace ManuscriptAudit.EtaleDisjointPullbackSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleObjectRestriction
open EtaleContinuousDirectImageMaps (baseChangeMap baseChangeMap_fst baseChangeMap_snd)

noncomputable section
universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T Y : Scheme.{u}} (q : Y ⟶ T)
variable {I : Type v} {B : I → Scheme.{u}} (i : ∀ a, B a ⟶ Y)
variable [∀ a, Etale (i a)]

/-- The component of a chart pullback lying on the specified branch. -/
abbrev piece (W : T.Etale) (a : I) : Y.Etale :=
  (postcompose (i a)).obj ((etaleBaseChange (i a ≫ q)).obj W)

/-- The native inclusion of the branch into the pullback chart. -/
def leg (W : T.Etale) (a : I) : piece q i W a ⟶ (etaleBaseChange q).obj W :=
  MorphismProperty.Over.homMk (baseChangeMap (i a) rfl W) (baseChangeMap_snd (i a) rfl W)

private theorem leg_isPullback (W : T.Etale) (a : I) :
    IsPullback (leg q i W a).left (pullback.snd W.hom (i a ≫ q))
      (pullback.snd W.hom q) (i a) := by
  have h : IsPullback ((leg q i W a).left ≫ pullback.fst W.hom q)
      (pullback.snd W.hom (i a ≫ q)) W.hom (i a ≫ q) := by
    change IsPullback (baseChangeMap (i a) rfl W ≫ pullback.fst W.hom q)
      (pullback.snd W.hom (i a ≫ q)) W.hom (i a ≫ q)
    rw [baseChangeMap_fst]
    exact IsPullback.of_hasPullback _ _
  exact h.of_right (baseChangeMap_snd (i a) rfl W) (IsPullback.of_hasPullback W.hom q)

private theorem leg_jointly_surjective
    (cover : ∀ y : Y, ∃ (a : I) (b : B a), i a b = y) (W : T.Etale) :
    ∀ z : ((etaleBaseChange q).obj W).left,
      ∃ (a : I) (z' : (piece q i W a).left), (leg q i W a).left z' = z := by
  intro z
  obtain ⟨a, b, hb⟩ := cover (pullback.snd W.hom q z)
  let H := leg_isPullback q i W a
  obtain ⟨x, hx, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd W.hom q) (g := i a) z b hb.symm
  have he := congrArg
    (fun m : pullback (pullback.snd W.hom q) (i a) ⟶ ((etaleBaseChange q).obj W).left ↦ m x)
    H.isoPullback_inv_fst
  exact ⟨a, H.isoPullback.inv x, he.trans hx⟩

private theorem leg_mono [∀ a, Mono (i a)] (W : T.Etale) (a : I) :
    Mono (leg q i W a).left :=
  (MorphismProperty.monomorphisms Scheme).of_isPullback (leg_isPullback q i W a).flip
    (inferInstanceAs (Mono (i a)))

private theorem leg_disjoint
    (disjoint : ∀ a b, a ≠ b → Disjoint (Set.range (i a)) (Set.range (i b)))
    (W : T.Etale) (a b : I) (hab : a ≠ b) :
    Disjoint (Set.range (leg q i W a).left) (Set.range (leg q i W b).left) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have ea := congrArg (fun f : (piece q i W a).left ⟶ Y ↦ f x) (leg_isPullback q i W a).w
  have eb := congrArg (fun f : (piece q i W b).left ⟶ Y ↦ f y) (leg_isPullback q i W b).w
  have h := congrArg (pullback.snd W.hom q) hy
  exact Set.disjoint_left.mp (disjoint a b hab) ⟨_, ea.symm⟩ ⟨_, eb.symm.trans h⟩

variable (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
variable [∀ a, Mono (i a)]
variable (cover : ∀ y : Y, ∃ (a : I) (b : B a), i a b = y)
variable (disjoint : ∀ a b, a ≠ b → Disjoint (Set.range (i a)) (Set.range (i b)))

/-- Sections over the full pullback agree with the product of actual branch sections. -/
def sectionsEquiv (W : T.Etale) :
    (F.obj.obj (op ((etaleBaseChange q).obj W))) ≃+
      (∀ a, F.obj.obj (op (piece q i W a))) :=
  SmallEtaleDisjointSections.sectionsEquivOfDisjointCover F (leg q i W)
    (leg_jointly_surjective q i cover W) (leg_mono q i W) (leg_disjoint q i disjoint W)

@[simp] theorem sectionsEquiv_apply (W : T.Etale)
    (s : F.obj.obj (op ((etaleBaseChange q).obj W))) (a : I) :
    sectionsEquiv q i F cover disjoint W s a = F.obj.map (leg q i W a).op s :=
  rfl

end
end ManuscriptAudit.EtaleDisjointPullbackSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleDisjointPullbackSections.sectionsEquiv,
      ``ManuscriptAudit.EtaleDisjointPullbackSections.sectionsEquiv_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
