import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralGluing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! The actual diagonal restricted to the two distinct affine charts of
the integral nodal model is a closed immersion. -/

namespace ManuscriptAudit.NodalOverlapDiagonal

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralGluing NodalIntegralChartTransition
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R]

private abbrev A := zChart R
private abbrev B := yChart R
private abbrev D := zOverlap R
private abbrev i := Algebra.algHom R (A R) (D R)

/-- The ring homomorphism of the cross-chart diagonal. -/
def diagonalAlgHom : A R ⊗[R] B R →ₐ[R] D R :=
  Algebra.TensorProduct.lift (i R) (yInZ R) (fun _ _ => Commute.all ..)

private theorem y_times_inverse :
    i R (yZ R) * yZOinv R = 1 :=
  IsLocalization.Away.mul_invSelf (yZ R)

/-- Its surjectivity follows from the first chart and the coordinate
Z/Y on the second chart, which is the required inverse. -/
theorem diagonalAlgHom_surjective : Function.Surjective (diagonalAlgHom R) := by
  intro q
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (yZ R) q
  refine ⟨a ⊗ₜ[R] (zY R ^ n), ?_⟩
  rw [diagonalAlgHom, Algebra.TensorProduct.lift_tmul, map_pow, yInZ_z]
  change i R a * yZOinv R ^ n = q
  change q * i R (yZ R) ^ n = i R a at ha
  rw [← ha, mul_assoc, ← mul_pow, y_times_inverse, one_pow, mul_one]

def toProduct :
    overlapScheme R ⟶ pullback (chartToBase R false) (chartToBase R true) :=
  pullback.lift (overlapToZ R) (overlapToY R)
    ((overlapToZ_over R).trans (overlapToY_over R).symm)

private def toTensor := Spec.map (CommRingCat.ofHom (diagonalAlgHom R).toRingHom)

private theorem toTensor_toZ :
    toTensor R ≫
      Spec.map (CommRingCat.ofHom (algebraMap (A R) (A R ⊗[R] B R))) = overlapToZ R := by
  unfold toTensor overlapToZ
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change diagonalAlgHom R (a ⊗ₜ[R] (1 : B R)) = i R a
  rw [diagonalAlgHom, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

private theorem toTensor_toY :
    toTensor R ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B R →ₐ[R] A R ⊗[R] B R).toRingHom) = overlapToY R := by
  change Spec.map (CommRingCat.ofHom (diagonalAlgHom R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        B R →ₐ[R] A R ⊗[R] B R).toRingHom) =
    Spec.map (CommRingCat.ofHom (yToZ R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (B R) (yOverlap R)))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  change diagonalAlgHom R ((1 : A R) ⊗ₜ[R] b) =
    yToZ R (algebraMap (B R) (yOverlap R) b)
  rw [diagonalAlgHom, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
    yToZ_algebraMap]

private theorem toProduct_eq :
    toProduct R = toTensor R ≫ (pullbackSpecIso R (A R) (B R)).inv := by
  apply pullback.hom_ext
  · rw [toProduct, pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst']
    exact (toTensor_toZ R).symm
  · rw [toProduct, pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd]
    exact (toTensor_toY R).symm

/-- The cross-chart part of the diagonal of the glued model is closed. -/
theorem cross_chart_isClosedImmersion : IsClosedImmersion (toProduct R) := by
  rw [toProduct_eq]
  letI : IsClosedImmersion (toTensor R) :=
    IsClosedImmersion.spec_of_surjective _ (diagonalAlgHom_surjective R)
  infer_instance

end
end ManuscriptAudit.NodalOverlapDiagonal

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalOverlapDiagonal.diagonalAlgHom_surjective,
      ``ManuscriptAudit.NodalOverlapDiagonal.cross_chart_isClosedImmersion] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
