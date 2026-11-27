import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwo
import PrimalitySheafVerification.ManuscriptAudit.IntPrimeResidueFiber
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspNodalAffine
import PrimalitySheafVerification.ManuscriptAudit.CuspSmallEtaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-! The characteristic-two coordinate substitution identifies the
actual affine schemes and the canonical characteristic-two fibers of
the two integral affine equations. -/

namespace ManuscriptAudit.NodalCharacteristicTwoAffine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open NodalAffinePresentation (nodeX nodeY)
open IntPrimeResidueFiber (closedPoint canonicalFiberIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section AnyField

universe u
variable (K : Type u) [Field K] [CharP K 2]

private abbrev node := NodalConductor.coordinates K
private abbrev cusp := CuspPunctured.CuspSubalgebra K

abbrev cuspCube : cusp K :=
  ⟨(X : Polynomial K) ^ 3, Algebra.subset_adjoin (by simp)⟩

/-- The actual parametrized affine coordinate rings are identified by
the characteristic-two coordinate substitution. -/
def coordinateEquiv : node K ≃ₐ[K] cusp K :=
  (NodalAffinePresentation.coordinateEquiv K).symm.trans
    ((NodalCharacteristicTwo.affineRingEquiv K).trans
      (CuspDelta.paper2_cusp_coordinate_presentation K))

private theorem nodePresentation_x :
    NodalAffinePresentation.coordinateEquiv K
      (AdjoinRoot.of (NodalAffinePresentation.equation K) X) = nodeX K := by
  change NodalAffinePresentation.parameter K
    (AdjoinRoot.of (NodalAffinePresentation.equation K) X) = nodeX K
  rw [NodalAffinePresentation.parameter_base]
  exact Polynomial.aeval_X _

private theorem cusp_root_witness :
    (CuspDelta.cuspPlaneEquation K).eval₂ (Polynomial.aeval
      (CuspPunctured.cuspSquare K)).toRingHom (cuspCube K) = 0 := by
  simp only [CuspDelta.cuspPlaneEquation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_pow]
  change cuspCube K ^ 2 -
    (Polynomial.aeval (CuspPunctured.cuspSquare K) (X : Polynomial K)) ^ 3 = 0
  rw [Polynomial.aeval_X]
  apply Subtype.ext
  change ((X : Polynomial K) ^ 3) ^ 2 - ((X : Polynomial K) ^ 2) ^ 3 = 0
  ring

private theorem cuspPresentation_x :
    CuspDelta.paper2_cusp_coordinate_presentation K
      (AdjoinRoot.of (CuspDelta.cuspPlaneEquation K) X) = CuspPunctured.cuspSquare K := by
  change AdjoinRoot.liftAlgHom (CuspDelta.cuspPlaneEquation K)
    (Polynomial.aeval (CuspPunctured.cuspSquare K)) (cuspCube K) (cusp_root_witness K)
    (AdjoinRoot.of (CuspDelta.cuspPlaneEquation K) X) = CuspPunctured.cuspSquare K
  rw [AdjoinRoot.liftAlgHom_of, Polynomial.aeval_X]

private theorem cuspPresentation_y :
    CuspDelta.paper2_cusp_coordinate_presentation K
      (AdjoinRoot.root (CuspDelta.cuspPlaneEquation K)) = cuspCube K := by
  change AdjoinRoot.liftAlgHom (CuspDelta.cuspPlaneEquation K)
    (Polynomial.aeval (CuspPunctured.cuspSquare K)) (cuspCube K) (cusp_root_witness K)
    (AdjoinRoot.root (CuspDelta.cuspPlaneEquation K)) = cuspCube K
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem shiftedPresentation_x :
    NodalCharacteristicTwo.affineRingEquiv K
      (AdjoinRoot.of (NodalAffinePresentation.equation K) X) =
        AdjoinRoot.of (CuspDelta.cuspPlaneEquation K) X :=
  NodalCharacteristicTwo.affineRingEquiv_x K

private theorem shiftedPresentation_y :
    NodalCharacteristicTwo.affineRingEquiv K
      (AdjoinRoot.root (NodalAffinePresentation.equation K)) =
        AdjoinRoot.root (CuspDelta.cuspPlaneEquation K) +
          AdjoinRoot.of (CuspDelta.cuspPlaneEquation K) X :=
  NodalCharacteristicTwo.affineRingEquiv_y K

theorem coordinateEquiv_x : coordinateEquiv K (nodeX K) = CuspPunctured.cuspSquare K := by
  rw [← nodePresentation_x K]
  unfold coordinateEquiv
  rw [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.trans_apply]
  exact (congrArg (fun z : AdjoinRoot (CuspDelta.cuspPlaneEquation K) =>
    CuspDelta.paper2_cusp_coordinate_presentation K z) (shiftedPresentation_x K)).trans
      (cuspPresentation_x K)

theorem coordinateEquiv_y :
    coordinateEquiv K (nodeY K) = cuspCube K + CuspPunctured.cuspSquare K := by
  have hy : NodalAffinePresentation.coordinateEquiv K
      (AdjoinRoot.root (NodalAffinePresentation.equation K)) = nodeY K :=
    NodalAffinePresentation.parameter_root K
  rw [← hy]
  unfold coordinateEquiv
  rw [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.trans_apply]
  let e := CuspDelta.paper2_cusp_coordinate_presentation K
  have h := congrArg (fun z : AdjoinRoot (CuspDelta.cuspPlaneEquation K) => e z)
    (shiftedPresentation_y K)
  have hAdd := map_add e (AdjoinRoot.root (CuspDelta.cuspPlaneEquation K))
    (AdjoinRoot.of (CuspDelta.cuspPlaneEquation K) X)
  exact h.trans (hAdd.trans (congrArg₂ (· + ·) (cuspPresentation_y K) (cuspPresentation_x K)))

/-- Actual affine scheme isomorphism from the cusp to the characteristic-two node model. -/
def affineIso : CuspProperCompactification.affineCusp K ≅ NodalProjectiveClosure.affineNode K :=
  Scheme.Spec.mapIso (coordinateEquiv K).toCommRingCatIso.op

end AnyField

private abbrev base := Spec (CommRingCat.of ℤ)
private abbrev residueTwo := base.fromSpecResidueField (closedPoint 2)

/-- The canonical affine scheme fiber at the integer prime (2) of the
integral nodal equation equals the cusp fiber up to isomorphism. -/
def canonicalAffineFiberIso :
    pullback residueTwo IntegralCuspNodalAffine.nodalToInt ≅
      pullback residueTwo IntegralCuspNodalAffine.cuspToInt :=
  (canonicalFiberIso 2 IntegralCuspNodalAffine.nodalToInt).symm ≪≫
    IntegralCuspNodalAffine.nodeFiberIso (ZMod 2) ≪≫
    (affineIso (ZMod 2)).symm ≪≫
    (IntegralCuspNodalAffine.cuspFiberIso (ZMod 2)).symm ≪≫
    canonicalFiberIso 2 IntegralCuspNodalAffine.cuspToInt

section GeometricCoefficients

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K] [CharP K 2]

/-- Geometric affine degree-one cohomology vanishes with every cyclic
coefficient order invertible in characteristic two. -/
theorem affine_cyclic_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H ((constantSheaf (NodalProjectiveClosure.affineNode K).smallEtaleTopology
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))) 1) := by
  let e := SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
    (affineIso K).symm (AddCommGrpCat.of (ZMod d)) 1
  have h := CuspSmallEtaleCohomology.cusp_cyclic_HOne_subsingleton K 2 d
  exact ⟨fun a b => e.injective (h.elim _ _)⟩

end GeometricCoefficients

end
end ManuscriptAudit.NodalCharacteristicTwoAffine

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCharacteristicTwoAffine.coordinateEquiv_x,
      ``ManuscriptAudit.NodalCharacteristicTwoAffine.coordinateEquiv_y,
      ``ManuscriptAudit.NodalCharacteristicTwoAffine.affineIso,
      ``ManuscriptAudit.NodalCharacteristicTwoAffine.canonicalAffineFiberIso,
      ``ManuscriptAudit.NodalCharacteristicTwoAffine.affine_cyclic_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
