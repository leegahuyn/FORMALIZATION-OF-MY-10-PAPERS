import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Extension by zero on the small étale site

For an open immersion, composition includes the small étale category of
the open into that of the ambient scheme. Sheafification of left Kan
extension along its opposite gives the left adjoint to restriction.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Compose an étale scheme over the open with the open immersion. -/
abbrev etalePostcompose : U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (show Etale j from inferInstance)

private def postcomposeFullyFaithful : (etalePostcompose j).FullyFaithful where
  preimage f := MorphismProperty.Over.homMk f.left (by
    apply (cancel_mono j).mp
    simpa only [Category.assoc, MorphismProperty.Over.map_obj_hom] using
      MorphismProperty.Over.w f)
  map_preimage f := by ext <;> rfl
  preimage_map f := by ext <;> rfl

private def postcomposeDownwardsClosed {Y : U.Etale} {W : X.Etale}
    (f : W ⟶ (etalePostcompose j).obj Y) : Σ W' : U.Etale, (etalePostcompose j).obj W' ≅ W := by
  have h : (f.left ≫ Y.hom) ≫ j = W.hom := by
    simpa only [Category.assoc, MorphismProperty.Over.map_obj_hom] using
      MorphismProperty.Over.w f
  letI : Etale ((f.left ≫ Y.hom) ≫ j) := by
    rw [h]
    exact W.prop
  let W' : U.Etale :=
    MorphismProperty.Over.mk ⊤ (f.left ≫ Y.hom) (Etale.of_comp _ j)
  refine ⟨W', MorphismProperty.Over.isoMk (Iso.refl W.left) ?_⟩
  change 𝟙 W.left ≫ W.hom = (f.left ≫ Y.hom) ≫ j
  simpa only [Category.id_comp] using h.symm

theorem postcomposeCoverPreserving :
    CoverPreserving U.smallEtaleTopology X.smallEtaleTopology (etalePostcompose j) where
  cover_preserve {W S} hS := by
    obtain ⟨ι, Z, f, rfl⟩ := Sieve.exists_eq_ofArrows S
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hS
    rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    simpa only [MorphismProperty.Over.map_map_left] using hS

theorem postcomposeContinuous :
    (etalePostcompose j).IsContinuous U.smallEtaleTopology X.smallEtaleTopology := by
  letI := (postcomposeFullyFaithful j).full
  letI := (postcomposeFullyFaithful j).faithful
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed (etalePostcompose j) (postcomposeDownwardsClosed j))
    (postcomposeCoverPreserving j)

variable (C : Type v) [Category.{w} C]

/-- The restriction of a small étale sheaf to the open. -/
def restriction : Sheaf X.smallEtaleTopology C ⥤ Sheaf U.smallEtaleTopology C :=
  letI := postcomposeContinuous j
  (etalePostcompose j).sheafPushforwardContinuous C U.smallEtaleTopology X.smallEtaleTopology

variable [HasInitial C]

theorem hasPointwiseLeftKanExtension (P : U.Etaleᵒᵖ ⥤ C) :
    (etalePostcompose j).op.HasPointwiseLeftKanExtension P := by
  letI := (postcomposeFullyFaithful j).full
  letI := (postcomposeFullyFaithful j).faithful
  let G := (etalePostcompose j).op
  intro W
  classical
  by_cases h : Nonempty (CostructuredArrow G W)
  · obtain ⟨a⟩ := h
    obtain ⟨V, e⟩ := postcomposeDownwardsClosed j a.hom.unop
    have hV : G.HasPointwiseLeftKanExtensionAt P (G.obj (op V)) :=
      HasColimit.mk { cocone := _, isColimit := colimitOfDiagramTerminal
        CostructuredArrow.mkIdTerminal _ }
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

theorem hasLeftKanExtension (P : U.Etaleᵒᵖ ⥤ C) :
    (etalePostcompose j).op.HasLeftKanExtension P := by
  letI := hasPointwiseLeftKanExtension j C P
  infer_instance

variable [HasWeakSheafify X.smallEtaleTopology C]

/-- Extension by zero defined by sheafifying the left Kan extension of presheaves. -/
def extensionByZero : Sheaf U.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology C :=
  letI := postcomposeContinuous j
  letI := hasLeftKanExtension j C
  Functor.sheafPullbackConstruction.sheafPullback (etalePostcompose j) C
    U.smallEtaleTopology X.smallEtaleTopology

/-- Extension by zero is left adjoint to restriction along the open immersion. -/
def extensionByZeroAdjunction : extensionByZero j C ⊣ restriction j C :=
  letI := postcomposeContinuous j
  letI := hasLeftKanExtension j C
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etalePostcompose j) C
    U.smallEtaleTopology X.smallEtaleTopology

/-- The adjunction for the abelian sheaves used in étale cohomology. -/
def abelianExtensionByZeroAdjunction :
    extensionByZero j AddCommGrpCat.{u} ⊣ restriction j AddCommGrpCat.{u} :=
  extensionByZeroAdjunction j _

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.postcomposeCoverPreserving,
      ``ManuscriptAudit.OpenEtaleExtension.postcomposeContinuous,
      ``ManuscriptAudit.OpenEtaleExtension.abelianExtensionByZeroAdjunction] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
