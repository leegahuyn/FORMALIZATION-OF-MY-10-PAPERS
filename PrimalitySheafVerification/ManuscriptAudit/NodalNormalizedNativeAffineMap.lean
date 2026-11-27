import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeCharts
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationFiber

/-! The actual pullback of the proper normalization over the Z chart
is the original affine nodal normalization morphism. -/

namespace ManuscriptAudit.NodalNormalizedNativeAffineMap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (affineOpen)
open NodalProjectiveNormalization (normalizationMap)
open NodalNormalizedNativeCharts (zToNormalized zToAffine zToNormalized_isPullback)
open NodalNormalizationFiber (affineNormalization)
open NodalNormalizationZChart (punctureNormalizationZIso punctureNormalizationZIso_hom_snd)
open NodalRelativeNormalization (A B L polynomialEquivIntegralClosure)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

/-- The second projection from the actual polynomial Z chart of the
projective normalization is exactly the affine normalization ring map. -/
theorem zToAffine_eq :
    zToAffine K h2 = affineNormalization K := by
  let e := polynomialEquivIntegralClosure K h2
  let e' := AffineRelativeNormalizationScheme.normalizationSpecIso (A K) (L K)
  let f := AffineRelativeNormalizationScheme.structureMap (A K) (L K)
  let r := CommRingCat.ofHom e.symm.toRingHom
  change Spec.map r ≫ e'.inv ≫ (punctureNormalizationZIso K).hom ≫
      pullback.snd (normalizationMap K) (affineOpen K) =
    Spec.map (CommRingCat.ofHom (algebraMap (A K) (B K)))
  rw [punctureNormalizationZIso_hom_snd]
  change Spec.map r ≫ e'.inv ≫ f.fromNormalization = _
  have he : e'.inv ≫ f.fromNormalization =
      AffineRelativeNormalizationScheme.structureMap (A K) (integralClosure (A K) (L K)) :=
    AffineRelativeNormalizationScheme.normalizationSpecIso_inv_over (A K) (L K)
  rw [he]
  change Spec.map r ≫ Spec.map (CommRingCat.ofHom (algebraMap (A K) (integralClosure (A K) (L K)))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext e.symm.commutes)

/-- The original affine normalization is the actual Cartesian restriction. -/
theorem zToNormalized_affine_isPullback :
    IsPullback (zToNormalized K h2) (affineNormalization K) (normalizationMap K) (affineOpen K) := by
  rw [← zToAffine_eq K h2]
  exact zToNormalized_isPullback K h2

end
end ManuscriptAudit.NodalNormalizedNativeAffineMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedNativeAffineMap.zToAffine_eq,
      ``ManuscriptAudit.NodalNormalizedNativeAffineMap.zToNormalized_affine_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName ↦ !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
