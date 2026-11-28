import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.ProetaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDisjointSections

/-! A disjoint native open cover gives a section product on every direct-image chart. -/

namespace ManuscriptAudit.ProetaleDisjointPullbackSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange
open OpenProetaleExtension (proetalePostcompose)
open ProetaleContinuousDirectImageMaps (pullbackMap pullbackMap_snd pullbackMap_isPullback)

noncomputable section
universe v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T Y : Scheme.{0}} (q : Y ⟶ T)
variable {I : Type} {B : I → Scheme.{0}} (i : ∀ a, B a ⟶ Y)
variable [∀ a, IsOpenImmersion (i a)]

/-- The component of a chart pullback lying on the specified branch. -/
abbrev piece (W : T.ProEt) (a : I) : Y.ProEt :=
  (proetalePostcompose (i a)).obj ((baseChange (i a ≫ q)).obj W)

/-- The native inclusion of the branch into the pullback chart. -/
def leg (W : T.ProEt) (a : I) : piece q i W a ⟶ (baseChange q).obj W :=
  MorphismProperty.Over.homMk (pullbackMap W.hom (i a) rfl) (pullbackMap_snd W.hom (i a) rfl)

private theorem leg_isPullback (W : T.ProEt) (a : I) :
    IsPullback (leg q i W a).left (pullback.snd W.hom (i a ≫ q))
      (pullback.snd W.hom q) (i a) :=
  pullbackMap_isPullback W.hom (i a) rfl

private theorem leg_jointly_surjective
    (cover : ∀ y : Y, ∃ (a : I) (b : B a), i a b = y) (W : T.ProEt) :
    ∀ z : ((baseChange q).obj W).left,
      ∃ (a : I) (z' : (piece q i W a).left), (leg q i W a).left z' = z := by
  intro z
  obtain ⟨a, b, hb⟩ := cover (pullback.snd W.hom q z)
  let H := leg_isPullback q i W a
  obtain ⟨x, hx, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd W.hom q) (g := i a) z b hb.symm
  have he := congrArg
    (fun m : pullback (pullback.snd W.hom q) (i a) ⟶ ((baseChange q).obj W).left ↦ m x)
    H.isoPullback_inv_fst
  exact ⟨a, H.isoPullback.inv x, he.trans hx⟩

private theorem leg_mono [∀ a, Mono (i a)] (W : T.ProEt) (a : I) :
    Mono (leg q i W a).left :=
  (MorphismProperty.monomorphisms Scheme).of_isPullback (leg_isPullback q i W a).flip
    (inferInstanceAs (Mono (i a)))

private theorem leg_disjoint
    (disjoint : ∀ a b, a ≠ b → Disjoint (Set.range (i a)) (Set.range (i b)))
    (W : T.ProEt) (a b : I) (hab : a ≠ b) :
    Disjoint (Set.range (leg q i W a).left) (Set.range (leg q i W b).left) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have ea := congrArg (fun f : (piece q i W a).left ⟶ Y ↦ f x) (leg_isPullback q i W a).w
  have eb := congrArg (fun f : (piece q i W b).left ⟶ Y ↦ f y) (leg_isPullback q i W b).w
  have h := congrArg (pullback.snd W.hom q) hy
  exact Set.disjoint_left.mp (disjoint a b hab) ⟨_, ea.symm⟩ ⟨_, eb.symm.trans h⟩

private theorem leg_covering
    (cover : ∀ y : Y, ∃ (a : I) (b : B a), i a b = y) (W : T.ProEt) :
    Sieve.ofArrows (piece q i W) (leg q i W) ∈
      Scheme.ProEt.topology Y ((baseChange q).obj W) := by
  let F := Scheme.ProEt.forget Y ⋙ Over.forget Y
  apply Precoverage.generate_mem_toGrothendieck
  change (Presieve.ofArrows (piece q i W) (leg q i W)).map F ∈
    Scheme.proetalePrecoverage ((baseChange q).obj W).left
  rw [Presieve.map_ofArrows]
  apply Scheme.etalePrecoverage_le_proetalePrecoverage _
  change Presieve.ofArrows _ _ ∈ Scheme.precoverage @Etale _
  refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨
    leg_jointly_surjective q i cover W, fun a ↦ ?_⟩
  change Etale (leg q i W a).left
  letI : IsOpenImmersion (leg q i W a).left := MorphismProperty.of_isPullback
    (P := @IsOpenImmersion) (leg_isPullback q i W a).flip inferInstance
  infer_instance

variable (F : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{v})
variable [∀ a, Mono (i a)]
variable (cover : ∀ y : Y, ∃ (a : I) (b : B a), i a b = y)
variable (disjoint : ∀ a b, a ≠ b → Disjoint (Set.range (i a)) (Set.range (i b)))

/-- Sections over the full pullback agree with the product of actual branch sections. -/
def sectionsEquiv (W : T.ProEt) :
    (F.obj.obj (op ((baseChange q).obj W))) ≃+
      (∀ a, F.obj.obj (op (piece q i W a))) :=
  ProetaleDisjointSections.sectionsEquivOfDisjointCover F (leg q i W)
    (leg_covering q i cover W) (leg_mono q i W) (leg_disjoint q i disjoint W)

@[simp] theorem sectionsEquiv_apply (W : T.ProEt)
    (s : F.obj.obj (op ((baseChange q).obj W))) (a : I) :
    sectionsEquiv q i F cover disjoint W s a = F.obj.map (leg q i W a).op s :=
  rfl

end
end ManuscriptAudit.ProetaleDisjointPullbackSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleDisjointPullbackSections.sectionsEquiv,
      ``ManuscriptAudit.ProetaleDisjointPullbackSections.sectionsEquiv_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
