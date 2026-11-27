import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! A point restricts to an essentially small full dense subsite. -/

namespace ManuscriptAudit.DensePointRestriction

open CategoryTheory

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe w

variable {C D : Type*} [Category* C] [Category* D] [EssentiallySmall.{w} C]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.Full] [F.Faithful] [F.IsCoverDense K]
variable (Φ : K.Point.{w})

private theorem pointedAffineRefinement (x : Φ.fiber.Elements) :
    ∃ a : (F ⋙ Φ.fiber).Elements, Nonempty ((Functor.Elements.precomp F Φ.fiber).obj a ⟶ x) := by
  obtain ⟨Y, f, ⟨e⟩, y, hy⟩ :=
    Φ.jointly_surjective (Sieve.coverByImage F x.fst)
      (F.is_cover_of_isCoverDense K x.fst) x.snd
  let a := (F ⋙ Φ.fiber).elementsMk e.obj (Φ.fiber.map e.lift y)
  refine ⟨a, ⟨⟨e.map, ?_⟩⟩⟩
  change Φ.fiber.map e.map (Φ.fiber.map e.lift y) = x.snd
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, e.fac]
  exact hy

private theorem restrictedCofiltered : IsCofiltered (F ⋙ Φ.fiber).Elements := by
  let E := Functor.Elements.precomp F Φ.fiber
  letI : E.Full := by
    constructor
    intro a b g
    let f : a.fst ⟶ b.fst := F.preimage g.val
    have hf : F.map f = g.val := F.map_preimage g.val
    have h : (F ⋙ Φ.fiber).map f a.snd = b.snd := by
      change Φ.fiber.map (F.map f) a.snd = b.snd
      exact (congrArg (fun m ↦ Φ.fiber.map m a.snd) hf).trans g.property
    refine ⟨⟨f, h⟩, Subtype.ext hf⟩
  letI : E.Faithful := by
    constructor
    intro a b f g h
    apply Subtype.ext
    apply F.map_injective
    exact congrArg (fun m ↦ m.val) h
  exact IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful E (pointedAffineRefinement F Φ)

/-- The actual restricted fiber is again a point of the dense subsite. -/
def restrict (hF : CoverPreserving J K F) : J.Point.{w} where
  fiber := F ⋙ Φ.fiber
  isCofiltered := restrictedCofiltered F Φ
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective {X} R hR x := by
    obtain ⟨Y, f, ⟨W, g, h, hg, rfl⟩, y, hy⟩ :=
      Φ.jointly_surjective (Sieve.functorPushforward F R) (hF.cover_preserve hR) x
    refine ⟨W, g, hg, Φ.fiber.map h y, ?_⟩
    change Φ.fiber.map (F.map g) (Φ.fiber.map h y) = x
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
    exact hy

variable (S : AlgebraicGeometry.Scheme.{w})

/-- The point obtained by restricting a small étale point to affine neighborhoods. -/
def affineEtalePoint (Ψ : S.smallEtaleTopology.Point.{w}) :
    (AlgebraicGeometry.Scheme.AffineEtale.topology S).Point.{w} :=
  restrict (AlgebraicGeometry.Scheme.AffineEtale.Spec S) Ψ
    (Functor.IsDenseSubsite.coverPreserving
      (AlgebraicGeometry.Scheme.AffineEtale.topology S)
      S.smallEtaleTopology (AlgebraicGeometry.Scheme.AffineEtale.Spec S))

end

end ManuscriptAudit.DensePointRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DensePointRestriction.restrict,
      ``ManuscriptAudit.DensePointRestriction.affineEtalePoint] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
