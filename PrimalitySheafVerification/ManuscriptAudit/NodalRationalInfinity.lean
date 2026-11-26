import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspInfinitySupport
import PrimalitySheafVerification.ManuscriptAudit.NodalProperYChart
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveBoundary

/-! The point x=z=0 in the Y=1 chart gives an actual K-rational closed
point on the proper nodal curve, with complement exactly the affine
Z-chart. -/

namespace ManuscriptAudit.NodalRationalInfinity

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspYChartAlgebra (PlaneRing grading y X_mem_one yChartι)
open CuspProperCompactification (projectivePlaneToBase)
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase projectiveNode_isProper
  affineOpen nodeInPlane)
open NodalProperYChart (chartOpen chartOpen_inPlane chartOpen_preimage_affine)
open NodalYChartImmersion (yEquation yCoordinateRing xCoeff zCoeff nodeYChart nodeToYChart
  nodeYInPlane evalYChart evalYChart_mk evalYPolynomial)
open NodalProjectiveBoundary (boundary_plane_coordinates)

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

private def polynomialAtOrigin : Polynomial K →ₐ[K] K := Polynomial.aeval (0 : K)

private theorem equation_at_origin :
    (yEquation K).eval₂ (polynomialAtOrigin K) (0 : K) = 0 := by
  unfold yEquation
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_C]
  simp only [mul_zero, zero_sub]
  change -(polynomialAtOrigin K ((Polynomial.X : Polynomial K) ^ 3)) = 0
  rw [map_pow]
  change -(Polynomial.aeval (0 : K) (Polynomial.X : Polynomial K) ^ 3) = 0
  rw [Polynomial.aeval_X]
  norm_num

private def coordinateAtOrigin : yCoordinateRing K →ₐ[K] K :=
  AdjoinRoot.liftAlgHom (yEquation K) (polynomialAtOrigin K) 0 (equation_at_origin K)

private theorem coordinateAtOrigin_x : coordinateAtOrigin K (xCoeff K) = 0 :=
  (AdjoinRoot.liftAlgHom_of (yEquation K) (polynomialAtOrigin K) 0
    (equation_at_origin K) (Polynomial.X : Polynomial K)).trans (Polynomial.aeval_X (0 : K))

private def originInChart : Spec (CommRingCat.of K) ⟶ nodeYChart K :=
  Spec.map (CommRingCat.ofHom (coordinateAtOrigin K).toRingHom)

/-- The rational point [0:1:0] on the actual proper nodal curve. -/
def infinityPoint : Spec (CommRingCat.of K) ⟶ projectiveNode K :=
  originInChart K ≫ chartOpen K

private theorem C_mem_zero (a : K) : (MvPolynomial.C a : PlaneRing K) ∈ grading K 0 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C (Fin 3) a)

private def planeConstants : K →+* grading K 0 where
  toFun a := ⟨MvPolynomial.C a, C_mem_zero K a⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)

private theorem infinity_chart_overBase :
    originInChart K ≫ nodeYInPlane K ≫ projectivePlaneToBase K =
      𝟙 (Spec (CommRingCat.of K)) := by
  change originInChart K ≫ nodeToYChart K ≫ yChartι K ≫
    Proj.toSpecZero (grading K) ≫ Spec.map (CommRingCat.ofHom (planeConstants K)) = _
  unfold originInChart nodeToYChart yChartι
  simp only [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change coordinateAtOrigin K (evalYChart K (fromZeroRingHom (grading K) _ (planeConstants K a))) = a
  change coordinateAtOrigin K (evalYChart K
    (Away.mk (grading K) (X_mem_one K 1) 0 (MvPolynomial.C a)
      (by simpa only [zero_nsmul] using C_mem_zero K a))) = a
  rw [evalYChart_mk]
  change coordinateAtOrigin K ((MvPolynomial.aeval _) (MvPolynomial.C a)) = a
  rw [MvPolynomial.aeval_C]
  exact (coordinateAtOrigin K).commutes a

/-- The infinity point is a section of the actual scheme structure map. -/
theorem infinityPoint_overBase :
    infinityPoint K ≫ projectiveNodeToBase K = 𝟙 (Spec (CommRingCat.of K)) := by
  unfold infinityPoint projectiveNodeToBase
  simpa only [Category.assoc, ← chartOpen_inPlane K] using infinity_chart_overBase K

theorem infinityPoint_isClosedImmersion : IsClosedImmersion (infinityPoint K) := by
  letI := projectiveNode_isProper K
  haveI : IsClosedImmersion (infinityPoint K ≫ projectiveNodeToBase K) := by
    rw [infinityPoint_overBase]
    infer_instance
  exact IsClosedImmersion.of_comp (infinityPoint K) (projectiveNodeToBase K)

theorem infinityPoint_outside :
    infinityPoint K (IsLocalRing.closedPoint K) ∉ Set.range (affineOpen K) := by
  intro hp
  change originInChart K (IsLocalRing.closedPoint K) ∈
    (chartOpen K) ⁻¹ᵁ (affineOpen K).opensRange at hp
  rw [chartOpen_preimage_affine] at hp
  change IsLocalRing.closedPoint K ∈
    (originInChart K) ⁻¹ᵁ PrimeSpectrum.basicOpen (xCoeff K) at hp
  unfold originInChart at hp
  rw [SpecMap_preimage_basicOpen] at hp
  have hnot := (PrimeSpectrum.mem_basicOpen _ _).mp hp
  apply hnot
  change coordinateAtOrigin K (xCoeff K) ∈ (IsLocalRing.closedPoint K).asIdeal
  rw [coordinateAtOrigin_x]
  exact (IsLocalRing.closedPoint K).asIdeal.zero_mem

theorem boundary_eq_infinityPoint (p : projectiveNode K)
    (hp : p ∉ Set.range (affineOpen K)) :
    p = infinityPoint K (IsLocalRing.closedPoint K) := by
  obtain ⟨hX, hZ, hY⟩ := boundary_plane_coordinates K p hp
  obtain ⟨hiX, hiZ, hiY⟩ := boundary_plane_coordinates K _ (infinityPoint_outside K)
  apply (nodeInPlane K).imageι.isClosedEmbedding.injective
  exact CuspInfinitySupport.projectivePlane_infinity_unique K _ _ hX hZ hY hiX hiZ hiY

/-- The actual boundary support is exactly this rational closed point. -/
theorem affine_complement_eq_infinity :
    (Set.range (affineOpen K))ᶜ = Set.range (infinityPoint K) := by
  ext p
  constructor
  · intro hp
    exact ⟨IsLocalRing.closedPoint K, (boundary_eq_infinityPoint K p hp).symm⟩
  · rintro ⟨q, rfl⟩
    have hq : q = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hq]
    exact infinityPoint_outside K

end
end ManuscriptAudit.NodalRationalInfinity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalRationalInfinity.infinityPoint_overBase,
      ``ManuscriptAudit.NodalRationalInfinity.infinityPoint_isClosedImmersion,
      ``ManuscriptAudit.NodalRationalInfinity.infinityPoint_outside,
      ``ManuscriptAudit.NodalRationalInfinity.affine_complement_eq_infinity] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
