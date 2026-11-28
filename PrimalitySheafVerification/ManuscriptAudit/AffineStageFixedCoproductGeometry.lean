import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFixedCoproductSquare
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! The coproducts used to descend the section's matching data are
actual affine étale covers and actual affine self-intersections. -/

namespace ManuscriptAudit.AffineStageFixedCoproductGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : CommRingCat.{u}}

abbrev left (B E : Under R) : B ⟶ B ⨿ E := coprod.inl
abbrev right (B E : Under R) : E ⟶ B ⨿ E := coprod.inr

abbrev overlapLeft (B E : Under R) : B ⨿ E ⟶ B ⨿ (E ⨿ E) :=
  coprod.map (𝟙 B) coprod.inl

abbrev overlapRight (B E : Under R) : B ⨿ E ⟶ B ⨿ (E ⨿ E) :=
  coprod.map (𝟙 B) coprod.inr

/-- The actual scheme underlying the fixed-base model cover is its
affine base change from the initial stage. -/
theorem isPullback_cover (B E : Under R) :
    IsPullback (Spec.map (left B E).right) (Spec.map (right B E).right)
      (Spec.map B.hom) (Spec.map E.hom) := by
  let hI := Under.mkIdInitial (X := R)
  have h : IsPushout (hI.to B) (hI.to E) (left B E) (right B E) :=
    IsPushout.of_is_coproduct' (colimit.isColimit _) hI
  have g := h.map (Under.forget R)
  change IsPushout (hI.to B).right (hI.to E).right (left B E).right (right B E).right at g
  rw [Under.mkIdInitial_to_right, Under.mkIdInitial_to_right] at g
  exact isPullback_SpecMap_of_isPushout _ _ _ _ g

/-- The cover morphism is a literal étale morphism when the given
fixed model is étale. -/
theorem etale_cover (B E : Under R) (hE : Etale (Spec.map E.hom)) :
    Etale (Spec.map (left B E).right) :=
  MorphismProperty.of_isPullback (P := @Etale) (isPullback_cover B E).flip hE

/-- The two maps of the self-intersection are the actual pullback legs. -/
theorem isPullback_overlap (B E : Under R) :
    IsPullback (Spec.map (overlapLeft B E).right) (Spec.map (overlapRight B E).right)
      (Spec.map (left B E).right) (Spec.map (left B E).right) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    ((AffineStageFixedCoproductSquare.isPushout B E).map (Under.forget R))

/-- Actual surjectivity persists under each later refinement of the base. -/
theorem surjective_refinement {B C : Under R} (t : B ⟶ C) (E : Under R)
    (h : Function.Surjective (Spec.map (left B E).right)) :
    Function.Surjective (Spec.map (left C E).right) := by
  have g := (IsPushout.of_coprod_inl_with_id t E).map (Under.forget R)
  have hg : IsPullback (Spec.map (coprod.map t (𝟙 E)).right) (Spec.map (left C E).right)
      (Spec.map (left B E).right) (Spec.map t.right) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ g
  have h' : Surjective (Spec.map (left C E).right) :=
    MorphismProperty.of_isPullback (P := @Surjective) hg ⟨h⟩
  exact h'.surj

end
end ManuscriptAudit.AffineStageFixedCoproductGeometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineStageFixedCoproductGeometry.etale_cover,
      ``ManuscriptAudit.AffineStageFixedCoproductGeometry.isPullback_overlap,
      ``ManuscriptAudit.AffineStageFixedCoproductGeometry.surjective_refinement] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
