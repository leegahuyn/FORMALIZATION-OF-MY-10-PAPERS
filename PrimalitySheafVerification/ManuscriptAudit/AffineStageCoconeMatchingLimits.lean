import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFinitePresentationContinuity

/-! Finite matching data descend simultaneously on a cover diagram
and its self-intersection diagram over the same base. -/

namespace ManuscriptAudit.AffineStageCoconeMatchingLimits

open CategoryTheory CategoryTheory.Limits
open AffineStageFinitePresentationContinuity (exists_factorization exists_factorization_with_two_relations)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  {R : CommRingCat.{u}} {F G : J ⥤ Under R} {cF : Cocone F} {cG : Cocone G}

set_option maxHeartbeats 4300000 in
/-- An actual pair of compatible natural maps of diagrams detects
both matching triangles at one finite stage. -/
theorem exists_matching_stage (hF : IsColimit cF) (hG : IsColimit cG)
    (l r : F ⟶ G) (L H : cF.pt ⟶ cG.pt)
    (hl : ∀ i, cF.ι.app i ≫ L = l.app i ≫ cG.ι.app i)
    (hr : ∀ i, cF.ι.app i ≫ H = r.app i ≫ cG.ι.app i)
    (P Q : Under R) (hP : P.hom.hom.FinitePresentation) (hQ : Q.hom.hom.FinitePresentation)
    (a b : P ⟶ Q) (x : P ⟶ cF.pt) (y : Q ⟶ cG.pt)
    (h₁ : a ≫ y = x ≫ L) (h₂ : b ≫ y = x ≫ H) :
    ∃ (j : J) (v : P ⟶ F.obj j) (w : Q ⟶ G.obj j),
      v ≫ cF.ι.app j = x ∧ w ≫ cG.ι.app j = y ∧
        a ≫ w = v ≫ l.app j ∧ b ≫ w = v ≫ r.app j := by
  obtain ⟨i, x₀, hx₀⟩ := exists_factorization P hF hP x
  have e₁ : a ≫ y = (x₀ ≫ l.app i) ≫ cG.ι.app i := by
    calc
      _ = x ≫ L := h₁
      _ = (x₀ ≫ cF.ι.app i) ≫ L := congrArg (fun d ↦ d ≫ L) hx₀.symm
      _ = _ := by rw [Category.assoc, Category.assoc, hl]
  have e₂ : b ≫ y = (x₀ ≫ r.app i) ≫ cG.ι.app i := by
    calc
      _ = x ≫ H := h₂
      _ = (x₀ ≫ cF.ι.app i) ≫ H := congrArg (fun d ↦ d ≫ H) hx₀.symm
      _ = _ := by rw [Category.assoc, Category.assoc, hr]
  obtain ⟨j, ij, w, hw, ha, hb⟩ :=
    exists_factorization_with_two_relations P hG hP Q hQ (x₀ ≫ l.app i) (x₀ ≫ r.app i)
      a b y e₁ e₂
  refine ⟨j, x₀ ≫ F.map ij, w, ?_, hw, ?_, ?_⟩
  · rw [Category.assoc]
    exact (congrArg (fun d ↦ x₀ ≫ d) (cF.w ij)).trans hx₀
  · refine ha.trans ?_
    rw [Category.assoc, Category.assoc, l.naturality]
  · refine hb.trans ?_
    rw [Category.assoc, Category.assoc, r.naturality]

end
end ManuscriptAudit.AffineStageCoconeMatchingLimits

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineStageCoconeMatchingLimits.exists_matching_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
