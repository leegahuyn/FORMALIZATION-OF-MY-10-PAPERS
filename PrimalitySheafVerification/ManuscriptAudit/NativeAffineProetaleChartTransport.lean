import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawStageElements
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! Every object of the actual pro-étale site whose underlying scheme
is affine is canonically isomorphic to the chart of its coordinate ring. -/

namespace ManuscriptAudit.NativeAffineProetaleChartTransport

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleAffineTensor (spectrum structureMap object specMap)
open NativeAffineEtaleRawStageElements (chartMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

abbrev coordinateRing (W : (spectrum A).ProEt) : CommRingCat.{u} :=
  Scheme.Γ.obj (op W.left)

variable (W : (spectrum A).ProEt) [IsAffine W.left]

private abbrev m : Spec (coordinateRing W) ⟶ spectrum A := W.left.isoSpec.inv ≫ W.hom

private def coordinates : CommRingCat.of A ⟶ coordinateRing W := Spec.preimage (m W)

instance coordinateAlgebra : Algebra A (coordinateRing W) :=
  (coordinates W).hom.toAlgebra

theorem structureMap_eq : structureMap A (coordinateRing W) = m W :=
  Spec.map_preimage _

instance coordinate_weaklyEtale : WeaklyEtale (structureMap A (coordinateRing W)) := by
  rw [structureMap_eq]
  change WeaklyEtale (W.left.isoSpec.inv ≫ W.hom)
  infer_instance

/-- The geometric spectrum chart is an isomorphism in the actual site. -/
def chartIso : object A (coordinateRing W) ≅ W :=
  MorphismProperty.Over.isoMk W.left.isoSpec.symm (structureMap_eq W).symm

variable {W} {V : (spectrum A).ProEt} [IsAffine V.left]

private def coordinateHom (f : V ⟶ W) :
    CommRingCat.of (coordinateRing W) ⟶ CommRingCat.of (coordinateRing V) :=
  Spec.preimage ((chartIso V).hom.left ≫ f.left ≫ (chartIso W).inv.left)

private theorem coordinateHom_compat (f : V ⟶ W) :
    CommRingCat.ofHom (algebraMap A (coordinateRing W)) ≫ coordinateHom f =
      CommRingCat.ofHom (algebraMap A (coordinateRing V)) := by
  apply Spec.map_injective
  rw [Spec.map_comp, coordinateHom, Spec.map_preimage]
  change ((chartIso V).hom.left ≫ f.left ≫ (chartIso W).inv.left) ≫
    structureMap A (coordinateRing W) = structureMap A (coordinateRing V)
  have hw : (chartIso W).inv.left ≫ structureMap A (coordinateRing W) = W.hom :=
    MorphismProperty.Over.w (chartIso W).inv
  have hv : (chartIso V).hom.left ≫ V.hom = structureMap A (coordinateRing V) :=
    MorphismProperty.Over.w (chartIso V).hom
  rw [Category.assoc, Category.assoc, hw, MorphismProperty.Over.w f, hv]

/-- The algebra map underlying the affine chart presentation of an actual arrow. -/
def chartAlgebraMap (f : V ⟶ W) : coordinateRing W →ₐ[A] coordinateRing V where
  toRingHom := (coordinateHom f).hom
  commutes' r := DFunLike.congr_fun
    (congrArg (fun j : CommRingCat.of A ⟶ CommRingCat.of (coordinateRing V) ↦ j.hom)
      (coordinateHom_compat f)) r

/-- Chart coordinates conjugate the literal site arrow. -/
theorem chartIso_natural (f : V ⟶ W) :
    chartMap (chartAlgebraMap f) ≫ (chartIso W).hom = (chartIso V).hom ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (coordinateHom f) ≫ (chartIso W).hom.left =
    (chartIso V).hom.left ≫ f.left
  rw [coordinateHom, Spec.map_preimage, Category.assoc, Category.assoc]
  have h : (chartIso W).inv.left ≫ (chartIso W).hom.left = 𝟙 _ :=
    congrArg (fun a : W ⟶ W ↦ a.left) (chartIso W).inv_hom_id
  rw [h, Category.comp_id]

end
end ManuscriptAudit.NativeAffineProetaleChartTransport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineProetaleChartTransport.chartIso,
      ``ManuscriptAudit.NativeAffineProetaleChartTransport.chartIso_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
