import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityFunctionField
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityNeighborhood

/-! The actual projective generic point and its factorizations through
both opens of the Weierstrass cover. -/

namespace ManuscriptAudit.WeierstrassProjectiveGenericPoint

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassInfinityFunctionField
open WeierstrassInfinityOverlapPlane WeierstrassInfinityChartAlgebra

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

abbrev genericScheme := Spec (CommRingCat.of W.FunctionField)

def genericToAffine : genericScheme W ⟶ affineScheme W :=
  Spec.map (CommRingCat.ofHom (algebraMap W.CoordinateRing W.FunctionField))

/-- The generic-point morphism into the actual projective closure. -/
def genericPoint : genericScheme W ⟶ projectiveScheme W :=
  genericToAffine W ≫ affineOpen W

/-- The same generic point, expressed in the actual affine infinity chart. -/
def genericToNeighborhood : genericScheme W ⟶ WeierstrassCartierInfinity.neighborhoodScheme W :=
  Spec.map (CommRingCat.ofHom
    ((functionFieldEquiv W).symm.toRingHom.comp (algebraMap (Neighborhood W) (FractionRing (Neighborhood W)))))

private def genericToOverlap : genericScheme W ⟶ overlapScheme W :=
  Spec.map (CommRingCat.ofHom (affineOverlapToFunctionField W))

private theorem genericOverlap_affine :
    genericToOverlap W ≫ toAffine W = genericToAffine W := by
  unfold genericToOverlap toAffine genericToAffine
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (affineOverlapToFunctionField_base W)

private theorem genericOverlap_infinity :
    genericToOverlap W ≫ toInfinityChart W =
      genericToNeighborhood W ≫ WeierstrassCartierInfinity.neighborhoodToChart W := by
  unfold genericToOverlap toInfinityChart genericToNeighborhood
    WeierstrassCartierInfinity.neighborhoodToChart
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change yChartToFunctionField W x =
    (functionFieldEquiv W).symm (algebraMap (Neighborhood W) (FractionRing (Neighborhood W))
      (algebraMap (WeierstrassInfinityChartAlgebra.Ring W) (Neighborhood W) x))
  apply (functionFieldEquiv W).injective
  rw [RingEquiv.apply_symm_apply, functionFieldEquiv_yChart]

private theorem overlaps_in_projective :
    toAffine W ≫ affineOpen W = toInfinityChart W ≫ WeierstrassProperInfinityChart.chartOpen W := by
  apply (cancel_mono (inPlane W).imageι).mp
  rw [Category.assoc, Category.assoc, WeierstrassProperInfinityChart.chartOpen_inPlane]
  unfold affineOpen
  rw [Scheme.Hom.toImage_imageι]
  exact plane_overlap_eq W

/-- The affine and infinity charts give the same morphism from the common
generic point to the *actual* projective curve. -/
theorem genericPoint_factors_infinity :
    genericPoint W = genericToNeighborhood W ≫ WeierstrassCartierInfinity.neighborhoodOpen W := by
  unfold genericPoint WeierstrassCartierInfinity.neighborhoodOpen
  rw [← genericOverlap_affine, Category.assoc, overlaps_in_projective W,
    ← Category.assoc, genericOverlap_infinity W, Category.assoc]

end

end ManuscriptAudit.WeierstrassProjectiveGenericPoint

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassProjectiveGenericPoint.genericPoint_factors_infinity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
