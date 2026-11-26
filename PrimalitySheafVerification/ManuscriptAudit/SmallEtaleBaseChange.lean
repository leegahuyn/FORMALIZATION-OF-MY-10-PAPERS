import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Surjective base change on the small étale site

The small étale topology is detected by joint surjectivity of families.
For any surjective scheme morphism, base change preserves and reflects
covering sieves. An equivalence on the categories of étale objects
therefore induces an equivalence on sheaves with arbitrary coefficients.
-/

namespace ManuscriptAudit.SmallEtaleBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The pullback functor on schemes étale over the two bases. -/
abbrev etaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f

private theorem pullback_map_isPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Y.Etale} (g : A ⟶ B) :
    IsPullback ((etaleBaseChange f).map g).left (pullback.fst A.hom f)
      (pullback.fst B.hom f) g.left := by
  have hSnd : ((etaleBaseChange f).map g).left ≫ pullback.snd B.hom f =
      pullback.snd A.hom f := by
    simp only [etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
  have hFst : ((etaleBaseChange f).map g).left ≫ pullback.fst B.hom f =
      pullback.fst A.hom f ≫ g.left := by
    simp only [etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  refine IsPullback.of_right ?_ hFst (IsPullback.of_hasPullback B.hom f).flip
  rw [hSnd, MorphismProperty.Over.w g]
  exact (IsPullback.of_hasPullback A.hom f).flip

private theorem range_of_pullback_square {W Z P Q : Scheme.{u}}
    (a : W ⟶ Z) (b : W ⟶ P) (c : Z ⟶ Q) (d : P ⟶ Q) (h : IsPullback a b c d) :
    Set.range a = c ⁻¹' Set.range d := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨b x, ?_⟩
    change (b ≫ d) x = (a ≫ c) x
    exact congrArg (fun k : W ⟶ Q => k x) h.w.symm
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := d) z x hx.symm
    refine ⟨h.isoPullback.inv v, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]
    exact hv

private theorem range_pullback_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Y.Etale} (g : A ⟶ B) :
    Set.range ((etaleBaseChange f).map g).left =
      (pullback.fst B.hom f) ⁻¹' Set.range g.left :=
  range_of_pullback_square _ _ _ _ (pullback_map_isPullback f g)

private theorem pullback_fst_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective f) (B : Y.Etale) :
    Function.Surjective (pullback.fst B.hom f) := by
  intro b
  obtain ⟨x, hx⟩ := hf (B.hom b)
  obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.hom) (g := f) b x hx.symm
  exact ⟨z, hz⟩

/-- Base change along any scheme morphism preserves small étale coverings. -/
theorem coverPreserving {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (etaleBaseChange f) where
  cover_preserve {B S} hS := by
    obtain ⟨ι, A, g, rfl⟩ := Sieve.exists_eq_ofArrows S
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hS
    rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, range_pullback_map f, Set.mem_preimage] at hS ⊢
    intro b
    exact hS (pullback.fst B.hom f b)

/-- Surjective base change preserves and reflects small étale covering sieves. -/
theorem functorPushforward_mem_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective f) {B : Y.Etale} {S : Sieve B} :
    S.functorPushforward (etaleBaseChange f) ∈ X.smallEtaleTopology _ ↔
      S ∈ Y.smallEtaleTopology B := by
  obtain ⟨ι, A, g, rfl⟩ := Sieve.exists_eq_ofArrows S
  rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff,
    Scheme.ofArrows_mem_smallEtaleTopology_iff]
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, range_pullback_map f, Set.mem_preimage]
  constructor
  · intro h b
    obtain ⟨b', rfl⟩ := pullback_fst_surjective f hf B b
    exact h b'
  · intro h b
    exact h (pullback.fst B.hom f b)

/-- Surjective base change that is an equivalence of étale objects presents a dense subsite. -/
theorem isDenseSubsite {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Function.Surjective f)
    [(etaleBaseChange f).IsEquivalence] :
    (etaleBaseChange f).IsDenseSubsite Y.smallEtaleTopology X.smallEtaleTopology where
  functorPushforward_mem_iff := functorPushforward_mem_iff f hf

/-- Reindexing sheaves along surjective base change is an equivalence if base change is an
equivalence on étale objects. -/
def sheafEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Function.Surjective f)
    [(etaleBaseChange f).IsEquivalence] (C : Type v) [Category.{w} C] :
    Sheaf X.smallEtaleTopology C ≌ Sheaf Y.smallEtaleTopology C :=
  let e : X.Etale ≌ Y.Etale := (Functor.asEquivalence (etaleBaseChange f)).symm
  letI : e.inverse.IsDenseSubsite Y.smallEtaleTopology X.smallEtaleTopology := isDenseSubsite f hf
  Equivalence.sheafCongr X.smallEtaleTopology Y.smallEtaleTopology e C

/-- Base change on étale objects preserves finite limits. -/
theorem preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (etaleBaseChange f) := by
  let ex := Scheme.Etale.forget X
  let ey := Scheme.Etale.forget Y
  letI : PreservesFiniteLimits (ey ⋙ CategoryTheory.Over.pullback f) :=
    comp_preservesFiniteLimits _ _
  let c : etaleBaseChange f ⋙ ex ≅ ey ⋙ CategoryTheory.Over.pullback f :=
    MorphismProperty.Over.pullbackCompForgetIso (P := @AlgebraicGeometry.Etale) (Q := ⊤) f
  letI := preservesFiniteLimits_of_natIso c.symm
  exact preservesFiniteLimits_of_reflects_of_preserves (etaleBaseChange f) ex

/-- Base change along any scheme morphism is continuous on the small étale sites. -/
theorem isContinuous_of_baseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  letI := preservesFiniteLimits f
  letI := flat_of_preservesFiniteLimits (etaleBaseChange f)
  exact (Functor.isContinuous_iff_coverPreserving).2 (coverPreserving f)

/-- Base change along a surjective morphism is continuous on the small étale sites. -/
theorem isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) (_hf : Function.Surjective f) :
    (etaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  isContinuous_of_baseChange f

/-- The actual small étale direct image of a scheme morphism. -/
def directImage {X Y : Scheme.{u}} (f : X ⟶ Y) (C : Type v) [Category.{w} C] :
    Sheaf X.smallEtaleTopology C ⥤ Sheaf Y.smallEtaleTopology C :=
  letI := isContinuous_of_baseChange f
  (etaleBaseChange f).sheafPushforwardContinuous C Y.smallEtaleTopology X.smallEtaleTopology

/-- The actual small étale direct image along a surjective scheme morphism. -/
def sheafPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) (_hf : Function.Surjective f)
    (C : Type v) [Category.{w} C] :
    Sheaf X.smallEtaleTopology C ⥤ Sheaf Y.smallEtaleTopology C :=
  directImage f C

end

end ManuscriptAudit.SmallEtaleBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SmallEtaleBaseChange.coverPreserving,
      ``ManuscriptAudit.SmallEtaleBaseChange.functorPushforward_mem_iff,
      ``ManuscriptAudit.SmallEtaleBaseChange.isDenseSubsite,
      ``ManuscriptAudit.SmallEtaleBaseChange.sheafEquivalence,
      ``ManuscriptAudit.SmallEtaleBaseChange.preservesFiniteLimits,
      ``ManuscriptAudit.SmallEtaleBaseChange.isContinuous_of_baseChange,
      ``ManuscriptAudit.SmallEtaleBaseChange.isContinuous,
      ``ManuscriptAudit.SmallEtaleBaseChange.directImage,
      ``ManuscriptAudit.SmallEtaleBaseChange.sheafPushforward] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
