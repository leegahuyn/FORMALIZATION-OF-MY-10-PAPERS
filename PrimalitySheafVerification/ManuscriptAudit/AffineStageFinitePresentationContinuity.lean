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

include hc hP in
set_option maxHeartbeats 2600000 in
/-- This is descent through the given diagrams, including the
actual diagonal tensor diagrams used on the affine Čech terms. -/
theorem exists_factorization (f : P ⟶ c.pt) :
    ∃ (j : J) (g : P ⟶ D.obj j), g ≫ c.ι.app j = f := by
  obtain ⟨j, g, hg⟩ := Types.jointly_surjective_of_isColimit (homIsColimit P hc hP) f
  exact ⟨(E (J := J)).inverse.obj j, g, hg⟩

include hc hP in
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

include hc hP in
set_option maxHeartbeats 3300000 in
/-- Two commuting triangles at the limit descend together with their
common map. The theorem also applies to the actual tensor-square
diagram used to check a matching section on a cover. -/
theorem exists_factorization_with_two_relations
    (Q : Under R) (hQ : Q.hom.hom.FinitePresentation)
    {i : J} (p q : P ⟶ D.obj i) (a b : P ⟶ Q) (f : Q ⟶ c.pt)
    (h₁ : a ≫ f = p ≫ c.ι.app i) (h₂ : b ≫ f = q ≫ c.ι.app i) :
    ∃ (j : J) (ij : i ⟶ j) (g : Q ⟶ D.obj j),
      g ≫ c.ι.app j = f ∧
        a ≫ g = p ≫ D.map ij ∧ b ≫ g = q ≫ D.map ij := by
  obtain ⟨j, g, hg⟩ := exists_factorization Q hc hQ f
  let k := IsFiltered.max i j
  let ik := IsFiltered.leftToMax i j
  let jk := IsFiltered.rightToMax i j
  let v := g ≫ D.map jk
  have hv : v ≫ c.ι.app k = f := by
    simpa only [v, Category.assoc, c.w jk] using hg
  have h₁' : (a ≫ v) ≫ c.ι.app k = (p ≫ D.map ik) ≫ c.ι.app k := by
    simpa only [Category.assoc, hv, c.w ik] using h₁
  obtain ⟨k', kk', hK⟩ := exists_equalizer P hc hP (a ≫ v) (p ≫ D.map ik) h₁'
  let v' := v ≫ D.map kk'
  let ik' := ik ≫ kk'
  have hv' : v' ≫ c.ι.app k' = f := by
    simpa only [v', Category.assoc, c.w kk'] using hv
  have hK' : a ≫ v' = p ≫ D.map ik' := by
    simpa only [v', ik', Functor.map_comp, Category.assoc] using hK
  have h₂' : (b ≫ v') ≫ c.ι.app k' = (q ≫ D.map ik') ≫ c.ι.app k' := by
    simpa only [Category.assoc, hv', c.w ik'] using h₂
  obtain ⟨l, k'l, hL⟩ := exists_equalizer P hc hP (b ≫ v') (q ≫ D.map ik') h₂'
  refine ⟨l, ik' ≫ k'l, v' ≫ D.map k'l, ?_, ?_, ?_⟩
  · simpa only [Category.assoc, c.w k'l] using hv'
  · simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun m : P ⟶ D.obj k' ↦ m ≫ D.map k'l) hK'
  · simpa only [Functor.map_comp, Category.assoc] using hL

end
end ManuscriptAudit.AffineStageFinitePresentationContinuity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineStageFinitePresentationContinuity.exists_factorization,
      ``ManuscriptAudit.AffineStageFinitePresentationContinuity.exists_equalizer,
      ``ManuscriptAudit.AffineStageFinitePresentationContinuity.exists_factorization_with_two_relations] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
