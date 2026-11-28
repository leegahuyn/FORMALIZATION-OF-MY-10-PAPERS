import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFinitePresentationContinuity

/-! Two finite source equations detected at a filtered ring colimit
can be witnessed simultaneously at one later stage. -/

namespace ManuscriptAudit.AffineStageSimultaneousEqualities

open CategoryTheory CategoryTheory.Limits
open AffineStageFinitePresentationContinuity (exists_equalizer)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  {R : CommRingCat.{u}} {D : J ⥤ Under R} {c : Cocone D}

set_option maxHeartbeats 3600000 in
/-- Both pairs retain their precise common restricting stage. -/
theorem exists_two_equalizers (hc : IsColimit c) (P Q : Under R)
    (hP : P.hom.hom.FinitePresentation) (hQ : Q.hom.hom.FinitePresentation)
    {i : J} (a b : P ⟶ D.obj i) (x y : Q ⟶ D.obj i)
    (ha : a ≫ c.ι.app i = b ≫ c.ι.app i) (hx : x ≫ c.ι.app i = y ≫ c.ι.app i) :
    ∃ (j : J) (ij : i ⟶ j), a ≫ D.map ij = b ≫ D.map ij ∧ x ≫ D.map ij = y ≫ D.map ij := by
  obtain ⟨j, ij, hj⟩ := exists_equalizer P hc hP a b ha
  have h : (x ≫ D.map ij) ≫ c.ι.app j = (y ≫ D.map ij) ≫ c.ι.app j := by
    simpa only [Category.assoc, c.w] using! hx
  obtain ⟨k, jk, hk⟩ := exists_equalizer Q hc hQ _ _ h
  refine ⟨k, ij ≫ jk, ?_, ?_⟩
  · rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, hj]
  · simpa only [Functor.map_comp, Category.assoc] using hk

end
end ManuscriptAudit.AffineStageSimultaneousEqualities

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineStageSimultaneousEqualities.exists_two_equalizers
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
