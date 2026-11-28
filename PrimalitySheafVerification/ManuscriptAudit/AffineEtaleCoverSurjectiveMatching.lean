import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageSurjectiveModel
import PrimalitySheafVerification.ManuscriptAudit.AffineStageRefinementMatching

/-! A matching witness descends to a finite affine stage where
the original cover is still literally surjective. -/

namespace ManuscriptAudit.AffineEtaleCoverSurjectiveMatching

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineEtaleStageRefinementColimit (refinementDiagram refinementCocone isColimit_refinement)
open AffineStageFixedCoproductGeometry (left overlapLeft overlapRight)
open AffineStageRefinementMatching (coverCocone)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

variable (T : Stage A B) (E : Type u) [CommRing E]
  [Algebra T.carrier E] [Algebra.Etale T.carrier E]

private abbrev R := CommRingCat.of T.carrier
private abbrev k := CommRingCat.ofHom (algebraMap A T.carrier)
private abbrev C := refinementCocone T
private abbrev D := refinementDiagram T
private abbrev Q := CommRingCat.mkUnder (R T) E

set_option maxHeartbeats 5200000 in
/-- The pair of identities that produces a matching section descends
at a stage whose actual affine étale cover is surjective. -/
theorem exists_surjective_match (hApprox : FiniteTupleApproximation A B)
    (hSurj : Function.Surjective (Spec.map (left (C T).pt (Q T E)).right))
    (M N : Under (CommRingCat.of A)) (hM : M.hom.hom.FinitePresentation)
    (hN : N.hom.hom.FinitePresentation) (a b : M ⟶ N)
    (x : M ⟶ (coverCocone (k T) (C T) (Q T E)).pt)
    (y : N ⟶ (coverCocone (k T) (C T) (Q T E ⨿ Q T E)).pt)
    (h₁ : a ≫ y = x ≫ (Under.map (k T)).map (overlapLeft (C T).pt (Q T E)))
    (h₂ : b ≫ y = x ≫ (Under.map (k T)).map (overlapRight (C T).pt (Q T E))) :
    ∃ (j : Under T)
      (v : M ⟶ (Under.map (k T)).obj ((D T).obj j ⨿ Q T E))
      (w : N ⟶ (Under.map (k T)).obj ((D T).obj j ⨿ (Q T E ⨿ Q T E))),
      Function.Surjective (Spec.map (left ((D T).obj j) (Q T E)).right) ∧
        v ≫ (coverCocone (k T) (C T) (Q T E)).ι.app j = x ∧
        w ≫ (coverCocone (k T) (C T) (Q T E ⨿ Q T E)).ι.app j = y ∧
        a ≫ w = v ≫ (Under.map (k T)).map (overlapLeft ((D T).obj j) (Q T E)) ∧
        b ≫ w = v ≫ (Under.map (k T)).map (overlapRight ((D T).obj j) (Q T E)) := by
  obtain ⟨U, hU⟩ := AffineEtaleStageSurjectiveModel.exists_surjective_base T E hApprox hSurj
  let F := Under.forget U
  let e := equivSmallModel.{u} (Under T)
  letI : EssentiallySmall.{u} (Under U) := EssentiallySmall.mk' (Under.postEquiv (X := U) e)
  let d := (C T).whisker F
  have hC : IsColimit d :=
    (Functor.Final.isColimitWhiskerEquiv F (C T)).symm (isColimit_refinement T hApprox)
  obtain ⟨w', v, w, hv, hw, ha, hb⟩ :=
    AffineStageRefinementMatching.exists_refinement (k T) hC (Q T E)
      M N hM hN a b x y h₁ h₂
  exact ⟨w'.right, v, w, AffineStageFixedCoproductGeometry.surjective_refinement
    ((D T).map w'.hom) (Q T E) hU, hv, hw, ha, hb⟩

end
end ManuscriptAudit.AffineEtaleCoverSurjectiveMatching

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleCoverSurjectiveMatching.exists_surjective_match
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
