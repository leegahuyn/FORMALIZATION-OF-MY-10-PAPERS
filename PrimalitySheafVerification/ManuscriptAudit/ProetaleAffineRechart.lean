import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! An affine object over a spectrum has its actual coordinate algebra
as an affine chart in the small pro-étale site. -/

namespace ManuscriptAudit.ProetaleAffineRechart

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleAffineTensor

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A] (W : (spectrum A).ProEt) [IsAffine W.left]

abbrev coordinateRing : CommRingCat.{0} := Scheme.Γ.obj (op W.left)

private abbrev chartMap : Spec (coordinateRing A W) ⟶ spectrum A :=
  W.left.isoSpec.inv ≫ W.hom

private def ringMap : CommRingCat.of A ⟶ coordinateRing A W :=
  Spec.preimage (chartMap A W)

/-- The canonical algebra structure determined by the actual structural morphism. -/
instance coordinateAlgebra : Algebra A (coordinateRing A W) :=
  (ringMap A W).hom.toAlgebra

theorem structureMap_eq : structureMap A (coordinateRing A W) = chartMap A W :=
  Spec.map_preimage _

instance coordinateChartWeaklyEtale : WeaklyEtale (structureMap A (coordinateRing A W)) := by
  rw [structureMap_eq]
  change WeaklyEtale (W.left.isoSpec.inv ≫ W.hom)
  infer_instance

/-- The affine spectrum presentation over the same base. -/
def rechart : object A (coordinateRing A W) ⟶ W :=
  MorphismProperty.Over.homMk W.left.isoSpec.inv (structureMap_eq A W).symm

theorem rechart_comp_toTerminal (f : W ⟶ terminal A) :
    rechart A W ≫ f = toTerminal A (coordinateRing A W) := by
  apply MorphismProperty.Over.Hom.ext
  change W.left.isoSpec.inv ≫ f.left = structureMap A (coordinateRing A W)
  have hw : f.left = W.hom := by
    have h : f.left ≫ 𝟙 (spectrum A) = W.hom := MorphismProperty.Over.w f
    exact (Category.comp_id f.left).symm.trans h
  rw [hw, structureMap_eq]

theorem coordinateChartSurjective {f : W ⟶ terminal A} (hf : Surjective f.left) :
    Surjective (structureMap A (coordinateRing A W)) := by
  rw [structureMap_eq]
  have hw : f.left = W.hom := by
    have h : f.left ≫ 𝟙 (spectrum A) = W.hom := MorphismProperty.Over.w f
    exact (Category.comp_id f.left).symm.trans h
  change Surjective (W.left.isoSpec.inv ≫ W.hom)
  rw [← hw]
  letI : Surjective f.left := hf
  infer_instance

end
end ManuscriptAudit.ProetaleAffineRechart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineRechart.structureMap_eq,
      ``ManuscriptAudit.ProetaleAffineRechart.rechart_comp_toTerminal,
      ``ManuscriptAudit.ProetaleAffineRechart.coordinateChartSurjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
