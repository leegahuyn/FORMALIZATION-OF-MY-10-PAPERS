import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! Maps from an actual finitely presented algebra factor through a
stage of a filtered algebra colimit, and equal maps eventually agree. -/

namespace ManuscriptAudit.AffineStageFinitePresentationContinuity

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  {R : CommRingCat.{u}} {D : J ⥤ Under R} {c : Cocone D}
  (P : Under R) (hc : IsColimit c) (hP : P.hom.hom.FinitePresentation)

private abbrev E := equivSmallModel.{u} J

private abbrev homCocone :=
  (coyoneda.obj (op P)).mapCocone (c.whisker (E (J := J)).inverse)

private def homIsColimit : IsColimit (homCocone (c := c) P) := by
  let e := E (J := J)
  letI : IsFiltered (SmallModel.{u} J) := IsFiltered.of_equivalence e
  let H := e.inverse ⋙ D
  letI : PreservesColimit H (coyoneda.obj (op P)) :=
    CommRingCat.preservesColimit_coyoneda_of_finitePresentation R P hP H
  exact isColimitOfPreserves (coyoneda.obj (op P)) (hc.whiskerEquivalence e.symm)

set_option maxHeartbeats 2600000 in
/-- This is descent through the given diagrams, including the
actual diagonal tensor diagrams used on the affine Čech terms. -/
theorem exists_factorization (f : P ⟶ c.pt) :
    ∃ (j : J) (g : P ⟶ D.obj j), g ≫ c.ι.app j = f := by
  obtain ⟨j, g, hg⟩ := Types.jointly_surjective_of_isColimit (homIsColimit P hc hP) f
  exact ⟨(E (J := J)).inverse.obj j, g, hg⟩

set_option maxHeartbeats 2900000 in
/-- Equalities of the actual algebra homomorphisms are detected after
a single forward map in the given diagram. -/
theorem exists_equalizer {i : J} (f g : P ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a := by
  let e := E (J := J)
  letI : IsFiltered (SmallModel.{u} J) := IsFiltered.of_equivalence e
  let i' := e.functor.obj i
  let a : i ⟶ e.inverse.obj i' := (e.unitIso.app i).hom
  let f' := f ≫ D.map a
  let g' := g ≫ D.map a
  have h' : (homCocone (c := c) P).ι.app i' f' = (homCocone (c := c) P).ι.app i' g' := by
    change (f ≫ D.map a) ≫ c.ι.app (e.inverse.obj i') =
      (g ≫ D.map a) ≫ c.ι.app (e.inverse.obj i')
    simpa only [Category.assoc, c.w a] using h
  obtain ⟨j, b, hb⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (homIsColimit P hc hP) f' g').mp h'
  refine ⟨e.inverse.obj j, a ≫ e.inverse.map b, ?_⟩
  change (f ≫ D.map a) ≫ D.map (e.inverse.map b) =
    (g ≫ D.map a) ≫ D.map (e.inverse.map b) at hb
  simpa only [Functor.map_comp, Category.assoc] using hb

end
end ManuscriptAudit.AffineStageFinitePresentationContinuity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineStageFinitePresentationContinuity.exists_factorization,
      ``ManuscriptAudit.AffineStageFinitePresentationContinuity.exists_equalizer] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
