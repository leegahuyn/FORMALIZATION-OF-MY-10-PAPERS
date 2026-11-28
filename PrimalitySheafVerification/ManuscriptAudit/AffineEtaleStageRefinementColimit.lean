import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Category.Ring.Under.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageAlgebraColimit
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageSmall

/-! Refinements of a given actual affine étale stage are cofinal.
Their base changes, including those of a cover and its tensor square,
are actual colimit diagrams over that stage. -/

namespace ManuscriptAudit.AffineEtaleStageRefinementColimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage hom ringDiagram chartCocone)
open AffineEtaleStageColimit (FiniteTupleApproximation)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

variable (T : Stage A B)

private abbrev R := CommRingCat.of T.carrier

/-- The given affine stage has an actual filtered category of refinements. -/
instance refinement_essentiallySmall : EssentiallySmall.{u} (Under T) := by
  letI : EssentiallySmall.{u} (Stage A B) := NativeAffineEtaleStageSmall.essentiallySmall_stage
  let E := equivSmallModel.{u} (Stage A B)
  exact EssentiallySmall.mk' (Under.postEquiv (X := T) E)

/-- Reinterpret the actual stage refinements as algebras over the fixed stage. -/
abbrev refinementDiagram : Under T ⥤ Under (R T) :=
  Under.post (X := T) (ringDiagram (A := A) (B := B))

/-- The point is the actual chart algebra over the fixed stage. -/
def refinementCocone : Cocone (refinementDiagram T) where
  pt := Under.mk (CommRingCat.ofHom T.toChart.toRingHom)
  ι :=
    { app := fun W ↦ Under.homMk (CommRingCat.ofHom W.right.toChart.toRingHom)
        (CommRingCat.hom_ext (congrArg AlgHom.toRingHom W.hom.property))
      naturality := by
        intro U W f
        apply (Under.forget (R T)).map_injective
        change CommRingCat.ofHom (hom f.right).toRingHom ≫
          CommRingCat.ofHom W.right.toChart.toRingHom =
          CommRingCat.ofHom U.right.toChart.toRingHom ≫ 𝟙 (CommRingCat.of B)
        rw [Category.comp_id]
        exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom f.right.property) }

set_option maxHeartbeats 3000000 in
/-- The actual chart is the colimit of only the refinements
of the chosen affine stage. -/
def isColimit_refinement (hApprox : FiniteTupleApproximation A B) :
    IsColimit (refinementCocone T) := by
  letI : Nonempty (Under T) := ⟨Under.mk (𝟙 T)⟩
  apply AffineEtaleStageAlgebraColimit.liftIsColimit
  exact (Functor.Final.isColimitWhiskerEquiv (Under.forget T)
    (chartCocone (A := A) (B := B))).symm
      (AffineEtaleStageColimit.isColimit_chart hApprox)

/-- A base change to any fixed algebra over the initial stage,
in particular a cover ring or its tensor square, preserves this
actual colimit of the refinements. -/
def isColimit_baseChange (hApprox : FiniteTupleApproximation A B)
    (S : CommRingCat.{u}) [Algebra (R T) S] :
    IsColimit ((CommRingCat.tensorProd (R T) S).mapCocone (refinementCocone T)) := by
  letI : (CommRingCat.tensorProd (R T) S).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (CommRingCat.tensorProdIsoPushout (R T) S).symm
  exact isColimitOfPreserves _ (isColimit_refinement T hApprox)

end
end ManuscriptAudit.AffineEtaleStageRefinementColimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleStageRefinementColimit.isColimit_refinement,
      ``ManuscriptAudit.AffineEtaleStageRefinementColimit.isColimit_baseChange] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
