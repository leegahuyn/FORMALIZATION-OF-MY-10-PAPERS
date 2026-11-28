import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFixedCoproductLimits
import PrimalitySheafVerification.ManuscriptAudit.AffineStageCoconeMatchingLimits
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageAlgebraColimit

/-! A section's finite Čech matching data, measured over the original
base, descend together along refinements of the base of the étale model. -/

namespace ManuscriptAudit.AffineStageRefinementMatching

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  {A R : CommRingCat.{u}} (k : A ⟶ R)
  {F : J ⥤ Under R} {c : Cocone F}

private def forgetBaseColimit (hc : IsColimit c) :
    IsColimit ((Under.map k).mapCocone c) := by
  letI : Nonempty J := IsFiltered.nonempty
  letI : IsConnected J := IsFiltered.isConnected J
  apply AffineEtaleStageAlgebraColimit.liftIsColimit
  exact isColimitOfPreserves (Under.forget R) hc

/-- The literal cover after refinement and after forgetting to the original base. -/
abbrev coverCocone (c : Cocone F) (E : Under R) :=
  (Under.map k).mapCocone (AffineStageFixedCoproductLimits.cocone c E)

private abbrev L (B E : Under R) : B ⨿ E ⟶ B ⨿ (E ⨿ E) :=
  coprod.map (𝟙 B) coprod.inl

private abbrev H (B E : Under R) : B ⨿ E ⟶ B ⨿ (E ⨿ E) :=
  coprod.map (𝟙 B) coprod.inr

set_option maxHeartbeats 4900000 in
/-- The two overlap equations persist at one actual refining base
and use exactly its two self-pushout arrows. -/
theorem exists_refinement (hc : IsColimit c) (E : Under R)
    (M N : Under A) (hM : M.hom.hom.FinitePresentation) (hN : N.hom.hom.FinitePresentation)
    (a b : M ⟶ N) (x : M ⟶ (coverCocone k c E).pt)
    (y : N ⟶ (coverCocone k c (E ⨿ E)).pt)
    (h₁ : a ≫ y = x ≫ (Under.map k).map (L c.pt E))
    (h₂ : b ≫ y = x ≫ (Under.map k).map (H c.pt E)) :
    ∃ (j : J)
      (v : M ⟶ (Under.map k).obj (F.obj j ⨿ E))
      (w : N ⟶ (Under.map k).obj (F.obj j ⨿ (E ⨿ E))),
      v ≫ (coverCocone k c E).ι.app j = x ∧
        w ≫ (coverCocone k c (E ⨿ E)).ι.app j = y ∧
        a ≫ w = v ≫ (Under.map k).map (L (F.obj j) E) ∧
        b ≫ w = v ≫ (Under.map k).map (H (F.obj j) E) := by
  let l := whiskerRight (AffineStageFixedCoproductLimits.map F (coprod.inl : E ⟶ E ⨿ E))
    (Under.map k)
  let r := whiskerRight (AffineStageFixedCoproductLimits.map F (coprod.inr : E ⟶ E ⨿ E))
    (Under.map k)
  have hl (j : J) : (coverCocone k c E).ι.app j ≫ (Under.map k).map (L c.pt E) =
      l.app j ≫ (coverCocone k c (E ⨿ E)).ι.app j := by
    change (Under.map k).map _ ≫ (Under.map k).map _ =
      (Under.map k).map _ ≫ (Under.map k).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Under.map k).map (AffineStageFixedCoproductLimits.map_cocone c coprod.inl j)
  have hr (j : J) : (coverCocone k c E).ι.app j ≫ (Under.map k).map (H c.pt E) =
      r.app j ≫ (coverCocone k c (E ⨿ E)).ι.app j := by
    change (Under.map k).map _ ≫ (Under.map k).map _ =
      (Under.map k).map _ ≫ (Under.map k).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Under.map k).map (AffineStageFixedCoproductLimits.map_cocone c coprod.inr j)
  exact AffineStageCoconeMatchingLimits.exists_matching_stage
    (forgetBaseColimit k (AffineStageFixedCoproductLimits.isColimit hc E))
    (forgetBaseColimit k (AffineStageFixedCoproductLimits.isColimit hc (E ⨿ E)))
    l r _ _ hl hr M N hM hN a b x y h₁ h₂

end
end ManuscriptAudit.AffineStageRefinementMatching

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineStageRefinementMatching.exists_refinement
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
