import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Extension by zero on the small pro-étale site

For an open immersion, composition includes the small pro-pro-étale category of
the open into that of the ambient scheme. Sheafification of left Kan
extension along its opposite gives the left adjoint to restriction.
-/

namespace ManuscriptAudit.OpenProetaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Compose a weakly étale scheme over the open with the open immersion. -/
abbrev proetalePostcompose : U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (show WeaklyEtale j from inferInstance)

/-- Postcomposition along an open immersion is fully faithful on weakly étale objects. -/
def postcomposeFullyFaithful : (proetalePostcompose j).FullyFaithful where
  preimage f := MorphismProperty.Over.homMk f.left (by
    apply (cancel_mono j).mp
    simpa only [Category.assoc, MorphismProperty.Over.map_obj_hom] using
      MorphismProperty.Over.w f)
  map_preimage f := by
    apply (Scheme.ProEt.forget X).map_injective
    exact CostructuredArrow.hom_ext _ _ rfl
  preimage_map f := by
    apply (Scheme.ProEt.forget U).map_injective
    exact CostructuredArrow.hom_ext _ _ rfl

private def postcomposeDownwardsClosed {Y : U.ProEt} {W : X.ProEt}
    (f : W ⟶ (proetalePostcompose j).obj Y) : Σ W' : U.ProEt, (proetalePostcompose j).obj W' ≅ W := by
  have h : (f.left ≫ Y.hom) ≫ j = W.hom := by
    simpa only [Category.assoc, MorphismProperty.Over.map_obj_hom] using
      MorphismProperty.Over.w f
  letI : WeaklyEtale ((f.left ≫ Y.hom) ≫ j) := by
    rw [h]
    exact W.prop
  let W' : U.ProEt :=
    MorphismProperty.Over.mk ⊤ (f.left ≫ Y.hom) (WeaklyEtale.of_comp _ j)
  refine ⟨W', MorphismProperty.Over.isoMk (Iso.refl W.left) ?_⟩
  change 𝟙 W.left ≫ W.hom = (f.left ≫ Y.hom) ≫ j
  simpa only [Category.id_comp] using h.symm

/-- Composition with the open immersion preserves actual pro-étale covering sieves. -/
theorem postcomposeCoverPreserving :
    CoverPreserving (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) (proetalePostcompose j) where
  cover_preserve {W S} hS := by
    let F := proetalePostcompose j
    let G := Scheme.ProEt.forget U ⋙ Over.forget U
    let H := Scheme.ProEt.forget X ⋙ Over.forget X
    let J := Scheme.ProEt.precoverage U
    letI : J.IsStableUnderComposition := by
      change (Scheme.proetalePrecoverage.comap G).IsStableUnderComposition
      infer_instance
    letI : J.IsStableUnderBaseChange := by
      change (Scheme.proetalePrecoverage.comap G).IsStableUnderBaseChange
      infer_instance
    letI : J.HasIsos := by
      change (Scheme.proetalePrecoverage.comap G).HasIsos
      infer_instance
    obtain ⟨P, hP, hPS⟩ := (J.mem_toGrothendieck_iff_of_isStableUnderComposition).mp hS
    have h₀ : P.map G ∈ Scheme.proetalePrecoverage W.left := hP
    have h₁ : P.map F ∈ Scheme.ProEt.precoverage X (F.obj W) := by
      change (P.map F).map H ∈ Scheme.proetalePrecoverage W.left
      obtain ⟨ι, Y, f, rfl⟩ := P.exists_eq_ofArrows
      rw [Presieve.map_ofArrows, Presieve.map_ofArrows]
      simpa only [Presieve.map_ofArrows] using h₀
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck h₁)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨hf⟩
    exact Sieve.image_mem_functorPushforward _ _ (hPS _ _ hf)

theorem postcomposeContinuous :
    (proetalePostcompose j).IsContinuous (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) := by
  letI := (postcomposeFullyFaithful j).full
  letI := (postcomposeFullyFaithful j).faithful
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed (Scheme.ProEt.topology X)
      (proetalePostcompose j) (postcomposeDownwardsClosed j))
    (postcomposeCoverPreserving j)

variable (C : Type v) [Category.{w} C]

/-- The restriction of a small pro-étale sheaf to the open. -/
def restriction : Sheaf (Scheme.ProEt.topology X) C ⥤ Sheaf (Scheme.ProEt.topology U) C :=
  letI := postcomposeContinuous j
  (proetalePostcompose j).sheafPushforwardContinuous C (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

variable [HasInitial C]

theorem hasPointwiseLeftKanExtension (P : U.ProEtᵒᵖ ⥤ C) :
    (proetalePostcompose j).op.HasPointwiseLeftKanExtension P := by
  letI := (postcomposeFullyFaithful j).full
  letI := (postcomposeFullyFaithful j).faithful
  let G := (proetalePostcompose j).op
  intro W
  classical
  by_cases h : Nonempty (CostructuredArrow G W)
  · obtain ⟨a⟩ := h
    obtain ⟨V, e⟩ := postcomposeDownwardsClosed j a.hom.unop
    have hV : G.HasPointwiseLeftKanExtensionAt P (G.obj (op V)) :=
      HasColimit.mk
        { cocone := _
          isColimit := colimitOfDiagramTerminal CostructuredArrow.mkIdTerminal _ }
    exact (G.hasPointwiseLeftKanExtensionAt_iff_of_iso P e.op.symm).mp hV
  · have empty (a : CostructuredArrow G W) : False := h ⟨a⟩
    let c : Cocone (CostructuredArrow.proj G W ⋙ P) :=
      { pt := ⊥_ C
        ι := { app := fun a => (empty a).elim
               naturality := fun a _ _ => (empty a).elim } }
    exact HasColimit.mk
      { cocone := c
        isColimit :=
          { desc := fun s => initial.to s.pt
            fac := fun _ a => (empty a).elim
            uniq := fun _ g _ => initialIsInitial.hom_ext g _ } }

theorem hasLeftKanExtension (P : U.ProEtᵒᵖ ⥤ C) :
    (proetalePostcompose j).op.HasLeftKanExtension P := by
  letI := hasPointwiseLeftKanExtension j C P
  infer_instance

variable [HasWeakSheafify (Scheme.ProEt.topology X) C]

/-- Extension by zero defined by sheafifying the left Kan extension of presheaves. -/
def extensionByZero : Sheaf (Scheme.ProEt.topology U) C ⥤ Sheaf (Scheme.ProEt.topology X) C :=
  letI := postcomposeContinuous j
  letI := hasLeftKanExtension j C
  Functor.sheafPullbackConstruction.sheafPullback (proetalePostcompose j) C
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- Extension by zero is left adjoint to restriction along the open immersion. -/
def extensionByZeroAdjunction : extensionByZero j C ⊣ restriction j C :=
  letI := postcomposeContinuous j
  letI := hasLeftKanExtension j C
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (proetalePostcompose j) C
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The adjunction for the abelian sheaves used in pro-étale cohomology. -/
def abelianExtensionByZeroAdjunction :
    extensionByZero j AddCommGrpCat.{u + 1} ⊣ restriction j AddCommGrpCat.{u + 1} :=
  extensionByZeroAdjunction j _

end

end ManuscriptAudit.OpenProetaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenProetaleExtension.postcomposeCoverPreserving,
      ``ManuscriptAudit.OpenProetaleExtension.postcomposeContinuous,
      ``ManuscriptAudit.OpenProetaleExtension.abelianExtensionByZeroAdjunction] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
