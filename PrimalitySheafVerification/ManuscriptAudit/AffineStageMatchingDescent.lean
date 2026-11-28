import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFinitePresentationContinuity
import PrimalitySheafVerification.ManuscriptAudit.DiagonalCoproductColimit

/-! Matching along the two actual tensor-square arrows descends
to one relative affine stage, with both commuting triangles intact. -/

namespace ManuscriptAudit.AffineStageMatchingDescent

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  {R : CommRingCat.{u}} {D : J ⥤ Under R} {c : Cocone D}

set_option maxHeartbeats 3200000 in
/-- A finite algebra witness to a match on the actual limiting
self-intersection descends along a single relative stage refinement. -/
theorem exists_match_at_stage (hc : IsColimit c)
    (i : J) (hI : (D.obj i).hom.hom.FinitePresentation)
    (Q : Under R) (hQ : Q.hom.hom.FinitePresentation)
    (a b : D.obj i ⟶ Q) (g : Q ⟶ c.pt ⨿ c.pt)
    (hL : a ≫ g = c.ι.app i ≫ coprod.inl)
    (hR : b ≫ g = c.ι.app i ≫ coprod.inr) :
    ∃ (j : J) (ij : i ⟶ j) (v : Q ⟶ D.obj j ⨿ D.obj j),
      v ≫ coprod.map (c.ι.app j) (c.ι.app j) = g ∧
        a ≫ v = D.map ij ≫ coprod.inl ∧ b ≫ v = D.map ij ≫ coprod.inr := by
  let S := DiagonalCoproductColimit.cocone c c
  have hS := DiagonalCoproductColimit.isColimit hc hc
  have h₁ : a ≫ g = coprod.inl ≫ S.ι.app i := hL.trans (coprod.inl_map _ _).symm
  have h₂ : b ≫ g = coprod.inr ≫ S.ι.app i := hR.trans (coprod.inr_map _ _).symm
  obtain ⟨j, ij, v, hv, h₁', h₂'⟩ :=
    AffineStageFinitePresentationContinuity.exists_factorization_with_two_relations
      (D.obj i) hS hI Q hQ coprod.inl coprod.inr a b g h₁ h₂
  have hl : a ≫ v = coprod.inl ≫ coprod.map (D.map ij) (D.map ij) := h₁'
  have hr : b ≫ v = coprod.inr ≫ coprod.map (D.map ij) (D.map ij) := h₂'
  exact ⟨j, ij, v, hv, hl.trans (coprod.inl_map _ _), hr.trans (coprod.inr_map _ _)⟩

set_option maxHeartbeats 2800000 in
/-- When the two witnesses compare restrictions on the cover
itself, the same descent forces agreement at a common stage. -/
theorem exists_equal_at_stage (hc : IsColimit c)
    (i : J) (hI : (D.obj i).hom.hom.FinitePresentation)
    (Q : Under R) (hQ : Q.hom.hom.FinitePresentation)
    (a b : D.obj i ⟶ Q) (g : Q ⟶ c.pt)
    (hL : a ≫ g = c.ι.app i) (hR : b ≫ g = c.ι.app i) :
    ∃ (j : J) (ij : i ⟶ j) (v : Q ⟶ D.obj j), v ≫ c.ι.app j = g ∧
      a ≫ v = D.map ij ∧ b ≫ v = D.map ij := by
  have h₁ : a ≫ g = (𝟙 (D.obj i)) ≫ c.ι.app i := by rwa [Category.id_comp]
  have h₂ : b ≫ g = (𝟙 (D.obj i)) ≫ c.ι.app i := by rwa [Category.id_comp]
  obtain ⟨j, ij, v, hv, h₁', h₂'⟩ :=
    AffineStageFinitePresentationContinuity.exists_factorization_with_two_relations
      (D.obj i) hc hI Q hQ (𝟙 _) (𝟙 _) a b g h₁ h₂
  exact ⟨j, ij, v, hv, h₁'.trans (Category.id_comp _), h₂'.trans (Category.id_comp _)⟩

end
end ManuscriptAudit.AffineStageMatchingDescent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineStageMatchingDescent.exists_match_at_stage,
      ``ManuscriptAudit.AffineStageMatchingDescent.exists_equal_at_stage] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
