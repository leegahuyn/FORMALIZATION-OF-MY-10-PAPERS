import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Sheaf

/-! Refinements and section descent for native singleton covering sieves. -/

namespace ManuscriptAudit.SingletonCoverRefinement

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

abbrev Covers {U T : C} (f : U ⟶ T) := Sieve.generate (Presieve.singleton f) ∈ J T

/-- A pullback of a singleton cover is a singleton cover. -/
theorem cover_pullback_snd {V U T : C} (f : V ⟶ T) (g : U ⟶ T) [HasPullback f g]
    (hf : Covers J f) : Covers J (pullback.snd f g) := by
  have h := J.pullback_stable g hf
  rw [← Sieve.pullbackArrows_comm g (Presieve.singleton f), Presieve.pullback_singleton] at h
  exact h

/-- Singleton covers are stable under composition. -/
theorem cover_comp {W V T : C} (f : V ⟶ T) (g : W ⟶ V)
    (hf : Covers J f) (hg : Covers J g) : Covers J (g ≫ f) := by
  apply J.transitive hf
  intro U a ha
  obtain ⟨V', b, f', hf', rfl⟩ := ha
  cases hf'
  apply J.superset_covering _ (J.pullback_stable b hg)
  intro Z c hc
  change Sieve.generate (Presieve.singleton g) (c ≫ b) at hc
  obtain ⟨W', d, g', hg', hd⟩ := hc
  cases hg'
  refine ⟨W, d, g ≫ f, Presieve.singleton_self _, ?_⟩
  change d ≫ (g ≫ f) = c ≫ (b ≫ f)
  rw [← Category.assoc, hd, Category.assoc]

/-- Three maps to the target of a cover lift simultaneously after a
single common refinement of their source. -/
theorem exists_common_refinement [HasPullbacks C] {T W V : C}
    (g : V ⟶ W) (hg : Covers J g) (p₁ p₂ p₃ : T ⟶ W) :
    ∃ (R : C) (r : R ⟶ T), Covers J r ∧
      ∃ e₁ e₂ e₃ : R ⟶ V,
        e₁ ≫ g = r ≫ p₁ ∧ e₂ ≫ g = r ≫ p₂ ∧ e₃ ≫ g = r ≫ p₃ := by
  let R₁ := pullback g p₁
  let r₁ : R₁ ⟶ T := pullback.snd g p₁
  let R₂ := pullback g (r₁ ≫ p₂)
  let r₂ : R₂ ⟶ R₁ := pullback.snd g (r₁ ≫ p₂)
  let R₃ := pullback g ((r₂ ≫ r₁) ≫ p₃)
  let r₃ : R₃ ⟶ R₂ := pullback.snd g ((r₂ ≫ r₁) ≫ p₃)
  have h₁ : Covers J r₁ := cover_pullback_snd J g p₁ hg
  have h₂ : Covers J r₂ := cover_pullback_snd J g (r₁ ≫ p₂) hg
  have h₃ : Covers J r₃ := cover_pullback_snd J g ((r₂ ≫ r₁) ≫ p₃) hg
  refine ⟨R₃, r₃ ≫ r₂ ≫ r₁, cover_comp J (r₂ ≫ r₁) r₃
    (cover_comp J r₁ r₂ h₁ h₂) h₃, r₃ ≫ r₂ ≫ pullback.fst g p₁,
      r₃ ≫ pullback.fst g (r₁ ≫ p₂), pullback.fst g ((r₂ ≫ r₁) ≫ p₃), ?_, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition, r₁]
  · simp only [Category.assoc, pullback.condition, r₂]
  · simp only [Category.assoc, pullback.condition, r₃]

section Sections

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable (A : Sheaf J AddCommGrpCat.{w}) {U T : C} (f : U ⟶ T)

private theorem underlying_isSheaf : Presieve.IsSheaf J (A.obj ⋙ forget AddCommGrpCat.{w}) :=
  (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J (forget AddCommGrpCat.{w})).obj A).property

/-- A sheaf restriction along a singleton covering arrow is injective. -/
theorem restriction_injective (hf : Covers J f) : Function.Injective (A.obj.map f.op) :=
  Presieve.isSeparatedFor_singleton.mp
    ((underlying_isSheaf J A).isSheafFor _ hf).isSeparatedFor

/-- A section glues over a singleton cover when it agrees on the
native pairwise pullback. -/
theorem exists_amalgamation [HasPullback f f] (hf : Covers J f) (a : A.obj.obj (op U))
    (ha : A.obj.map (pullback.fst f f).op a = A.obj.map (pullback.snd f f).op a) :
    ∃ t : A.obj.obj (op T), A.obj.map f.op t = a := by
  have hy : ∀ {W : C} (b d : W ⟶ U), b ≫ f = d ≫ f →
      A.obj.map b.op a = A.obj.map d.op a := by
    intro W b d h
    let e := pullback.lift b d h
    have hproj := congrArg (fun y ↦ A.obj.map e.op y) ha
    simpa only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
      ← op_comp, pullback.lift_fst, pullback.lift_snd, e] using hproj
  obtain ⟨t, ht, _⟩ := (Presieve.isSheafFor_singleton.mp
    ((underlying_isSheaf J A).isSheafFor _ hf)) a hy
  exact ⟨t, ht⟩

end Sections

end ManuscriptAudit.SingletonCoverRefinement

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SingletonCoverRefinement.exists_common_refinement,
      ``ManuscriptAudit.SingletonCoverRefinement.exists_amalgamation] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
