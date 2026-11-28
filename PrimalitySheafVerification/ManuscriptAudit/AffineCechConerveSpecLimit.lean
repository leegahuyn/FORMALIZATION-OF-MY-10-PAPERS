import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Opposites
import PrimalitySheafVerification.ManuscriptAudit.AffineCechConerveFilteredColimit

/-! Taking spectra of the literal wide-pushout algebra conerve
gives the actual scheme wide pullback, with its real vertex maps. -/

namespace ManuscriptAudit.AffineCechConerveSpecLimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : CommRingCat.{u}} (f : Arrow (Under A)) (n : ℕ)

abbrev C := Under A
abbrev degree := f.cechConerve.obj ⦋n⦌
abbrev head : f.left ⟶ degree f n := WidePushout.head (fun _ : Fin (n + 1) ↦ f.hom)
abbrev vertex (i : Fin (n + 1)) : f.right ⟶ degree f n :=
  WidePushout.ι (fun _ : Fin (n + 1) ↦ f.hom) i

private abbrev D := WidePushoutShape.wideSpan f.left (fun _ : Fin (n + 1) ↦ f.right) fun _ ↦ f.hom
private abbrev K := WidePullbackShape (Fin (n + 1))
private abbrev E := widePullbackShapeOpEquiv (Fin (n + 1))
private abbrev DR := (E (n := n)).functor ⋙ D f n ⋙ Under.forget A
private abbrev DS := WidePullbackShape.wideCospan (Spec f.left.right)
  (fun _ : Fin (n + 1) ↦ Spec f.right.right) (fun _ ↦ Spec.map f.hom.right)

private def ringCocone : Cocone (DR f n) :=
  (Under.forget A).mapCocone ((colimit.cocone (D f n)).whisker (E (n := n)).functor)

private def ringColimit : IsColimit (ringCocone f n) :=
  isColimitOfPreserves (Under.forget A) ((colimit.isColimit (D f n)).whiskerEquivalence (E (n := n)))

private def specDiagramIso : (DR f n).rightOp ⋙ Scheme.Spec ≅ DS f n :=
  NatIso.ofComponents (fun i ↦ by cases i <;> exact Iso.refl _) (by
    intro i j g
    cases g with
    | id =>
      cases i <;> simp [DR, DS, WidePushoutShape.wideSpan, WidePullbackShape.wideCospan, Spec.map_id]
    | term k =>
      change Spec.map f.hom.right ≫ 𝟙 _ = 𝟙 _ ≫ Spec.map f.hom.right
      simp)

private def beforeIso : Cone ((DR f n).rightOp ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (coneRightOpOfCocone (ringCocone f n))

/-- This cone has exactly the original affine coordinate ring. -/
def specCone : WidePullbackCone (fun _ : Fin (n + 1) ↦ Spec.map f.hom.right) :=
  (Cone.postcompose (specDiagramIso f n).hom).obj (beforeIso f n)

set_option maxHeartbeats 5800000 in
/-- Applying actual affine spectra to the chosen algebra model
constructs the limiting scheme cone. -/
def isLimit_specCone : IsLimit (specCone f n) :=
  (IsLimit.postcomposeHomEquiv (specDiagramIso f n) (beforeIso f n)).symm
    (isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone (DR f n) (ringColimit f n)))

theorem specCone_π (i : Fin (n + 1)) : (specCone f n).π i = Spec.map (vertex f n i).right := by
  change Spec.map (vertex f n i).right ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem specCone_base : (specCone f n).base = Spec.map (head f n).right := by
  change Spec.map (head f n).right ≫ 𝟙 _ = _
  exact Category.comp_id _

end
end ManuscriptAudit.AffineCechConerveSpecLimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineCechConerveSpecLimit.isLimit_specCone
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
