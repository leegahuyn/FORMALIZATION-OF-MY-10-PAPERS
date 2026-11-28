import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.Under.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageColimit
import PrimalitySheafVerification.ManuscriptAudit.DiagonalCoproductColimit

/-! The actual stage ring colimit is also a colimit of algebras.
The actual coproduct-square diagram in this undercategory has the
coproduct-square colimit. -/

namespace ManuscriptAudit.AffineEtaleStageAlgebraColimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage hom chartCocone)
open AffineEtaleStageColimit (FiniteTupleApproximation)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Under a fixed base, any nonempty algebra diagram with a colimit
on the underlying rings has that same colimit as an algebra. -/
def liftIsColimit {J : Type*} [Category* J] [Nonempty J]
    {R : CommRingCat.{u}} {D : J ⥤ Under R} {c : Cocone D}
    (hc : IsColimit ((Under.forget R).mapCocone c)) : IsColimit c where
  desc d := Under.homMk (hc.desc ((Under.forget R).mapCocone d)) (by
    let j := Classical.choice (inferInstance : Nonempty J)
    have h := hc.fac ((Under.forget R).mapCocone d) j
    change (c.ι.app j).right ≫ hc.desc ((Under.forget R).mapCocone d) =
      (d.ι.app j).right at h
    calc
      _ = ((D.obj j).hom ≫ (c.ι.app j).right) ≫
          hc.desc ((Under.forget R).mapCocone d) :=
          congrArg (fun m : R ⟶ c.pt.right ↦ m ≫ hc.desc ((Under.forget R).mapCocone d))
            (Under.w (c.ι.app j)).symm
      _ = (D.obj j).hom ≫ (d.ι.app j).right := by rw [Category.assoc, h]
      _ = _ := Under.w _)
  fac d j := by
    apply (Under.forget R).map_injective
    exact hc.fac ((Under.forget R).mapCocone d) j
  uniq d f hf := by
    apply (Under.forget R).map_injective
    exact hc.uniq ((Under.forget R).mapCocone d) f.right
      (fun j ↦ congrArg (Under.forget R).map (hf j))

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The actual affine stages with their structural map from the base. -/
def algebraDiagram : Stage A B ⥤ Under (CommRingCat.of A) where
  obj T := CommRingCat.mkUnder (CommRingCat.of A) T.carrier
  map f := (hom f).toUnder
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone retains the given structural map on the limiting chart. -/
def algebraCocone : Cocone (algebraDiagram (A := A) (B := B)) where
  pt := CommRingCat.mkUnder (CommRingCat.of A) B
  ι :=
    { app := fun T ↦ T.toChart.toUnder
      naturality := by
        intro T S f
        apply (Under.forget (CommRingCat.of A)).map_injective
        change CommRingCat.ofHom (hom f).toRingHom ≫ CommRingCat.ofHom S.toChart.toRingHom =
          CommRingCat.ofHom T.toChart.toRingHom ≫ 𝟙 (CommRingCat.of B)
        rw [Category.comp_id]
        exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom f.property) }

variable [WeaklyEtale (structureMap A B)]

set_option maxHeartbeats 2200000 in
/-- The actual affine stage cocone is a colimit in algebras over A. -/
def isColimit_algebra (hApprox : FiniteTupleApproximation A B) :
    IsColimit (algebraCocone (A := A) (B := B)) := by
  letI : Nonempty (Stage A B) := ⟨Stage.of A B (Algebra.ofId A B)⟩
  exact liftIsColimit (AffineEtaleStageColimit.isColimit_chart hApprox)

/-- Taking the diagonal tensor square in the category of A-algebras
preserves the actual stage colimit. -/
def isColimit_square (hApprox : FiniteTupleApproximation A B) :
    IsColimit (DiagonalCoproductColimit.cocone
      (algebraCocone (A := A) (B := B)) (algebraCocone (A := A) (B := B))) :=
  DiagonalCoproductColimit.isColimit (isColimit_algebra hApprox) (isColimit_algebra hApprox)

end
end ManuscriptAudit.AffineEtaleStageAlgebraColimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleStageAlgebraColimit.isColimit_algebra,
      ``ManuscriptAudit.AffineEtaleStageAlgebraColimit.isColimit_square] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
