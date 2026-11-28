import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProjectiveNormalization
import PrimalitySheafVerification.ManuscriptAudit.CuspChartIntersectionMaps
import PrimalitySheafVerification.ManuscriptAudit.CuspLaurentIntegralClosure
import PrimalitySheafVerification.ManuscriptAudit.AffineRelativeNormalizationScheme

/-! The proper normalization on the original affine cusp chart is the
actual spectral normalization map of the polynomial parameter line. -/

namespace ManuscriptAudit.CuspProjectiveNormalizationAffine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (affineOpen)
open CuspProperYChart (lineOpen)
open CuspProjectiveNormalization (normalizationMap)
open CuspChartIntersection (overlapIsoLaurent)
open CuspChartIntersectionMaps (laurentToAffineCusp overlapIsoLaurent_inv_toAffineCusp)
open CuspLaurentIntegralClosure (A B L polynomialEquiv)
open AffineRelativeNormalizationScheme (structureMap normalizationSpecIso normalizationSpecIso_inv_over)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

private abbrev q := structureMap (A K) (L K)
private abbrev g := pullback.snd (lineOpen K) (affineOpen K)

private def inversionIso : Spec (CommRingCat.of (L K)) ≅ Spec (CommRingCat.of (L K)) :=
  Scheme.Spec.mapIso (LaurentPolynomial.invert (R := K)).toRingEquiv.toCommRingCatIso.op

private theorem inversion_comp :
    (inversionIso K).inv ≫ laurentToAffineCusp K = q K := by
  let a := CommRingCat.ofHom (LaurentPolynomial.invert (R := K)).toRingHom
  have h : a ≫ a = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact LaurentPolynomial.involutive_invert x
  change Spec.map a ≫ (Spec.map a ≫ q K) = _
  rw [← Category.assoc, ← Spec.map_comp, h, Spec.map_id, Category.id_comp]

private def punctureIso : Spec (CommRingCat.of (L K)) ≅ pullback (lineOpen K) (affineOpen K) :=
  (inversionIso K).symm ≪≫ (overlapIsoLaurent K).symm ≪≫
    pullbackSymmetry (affineOpen K) (lineOpen K)

private theorem punctureIso_hom_snd :
    (punctureIso K).hom ≫ g K = q K := by
  change ((inversionIso K).inv ≫ (overlapIsoLaurent K).inv ≫
    (pullbackSymmetry (affineOpen K) (lineOpen K)).hom) ≫ g K = _
  simp only [Category.assoc, g, pullbackSymmetry_hom_comp_snd,
    overlapIsoLaurent_inv_toAffineCusp]
  exact inversion_comp K

private def relativeAffineIso :
    (g K).normalization ≅ pullback (normalizationMap K) (affineOpen K) :=
  asIso ((lineOpen K).normalizationPullback (affineOpen K))

set_option maxHeartbeats 5300000 in
private def punctureNormalizationIso :
    (q K).normalization ≅ pullback (normalizationMap K) (affineOpen K) := by
  let f := q K
  let h := g K
  let e := punctureIso K
  have hf : f = e.hom ≫ h := (punctureIso_hom_snd K).symm
  have hh : h = e.inv ≫ f := by rw [hf, Iso.inv_hom_id_assoc]
  let u := f.normalizationDesc (e.hom ≫ h.toNormalization) h.fromNormalization
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]; exact hf)
  let v := h.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]; exact hh)
  let E : f.normalization ≅ h.normalization :=
    { hom := u
      inv := v
      hom_inv_id := by
        apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
        · simp [u, v, Category.assoc]
        · simp [u, v, Category.assoc]
        · simp
      inv_hom_id := by
        apply Scheme.Hom.normalization.hom_ext h _ _ h.fromNormalization
        · simp [u, v, Category.assoc]
        · simp [u, v, Category.assoc]
        · simp }
  exact E ≪≫ relativeAffineIso K

private theorem punctureNormalizationIso_hom_snd :
    (punctureNormalizationIso K).hom ≫ pullback.snd (normalizationMap K) (affineOpen K) =
      (q K).fromNormalization := by
  simp only [punctureNormalizationIso, relativeAffineIso, Iso.trans_hom, asIso_hom,
    Category.assoc, normalizationMap, Scheme.Hom.normalizationPullback_snd,
    Scheme.Hom.normalizationDesc_comp]

/-- The literal affine chart of the proper normalization is the polynomial parameter line. -/
def normalizationAffineIso :
    pullback (normalizationMap K) (affineOpen K) ≅ Spec (CommRingCat.of (B K)) :=
  (punctureNormalizationIso K).symm ≪≫ normalizationSpecIso (A K) (L K) ≪≫
    Scheme.Spec.mapIso (polynomialEquiv K).toRingEquiv.toCommRingCatIso.op

set_option maxHeartbeats 4900000 in
/-- On the affine cusp base, the projective normalization map is the original finite cusp map. -/
theorem normalizationAffineIso_inv_over :
    (normalizationAffineIso K).inv ≫ pullback.snd (normalizationMap K) (affineOpen K) =
      CuspScheme.cuspMap K := by
  let a := CommRingCat.ofHom (polynomialEquiv K).symm.toRingHom
  let e := normalizationSpecIso (A K) (L K)
  change (Spec.map a ≫ e.inv ≫ (punctureNormalizationIso K).hom) ≫
    pullback.snd (normalizationMap K) (affineOpen K) = _
  simp only [Category.assoc, punctureNormalizationIso_hom_snd]
  change Spec.map a ≫ (e.inv ≫ (q K).fromNormalization) = CuspScheme.cuspMap K
  have he : e.inv ≫ (q K).fromNormalization = structureMap (A K) (integralClosure (A K) (L K)) :=
    normalizationSpecIso_inv_over (A K) (L K)
  rw [he]
  change Spec.map a ≫ Spec.map (CommRingCat.ofHom (algebraMap (A K) (integralClosure (A K) (L K)))) =
    Spec.map (CuspScheme.inclusion K)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext (polynomialEquiv K).symm.commutes)

end
end ManuscriptAudit.CuspProjectiveNormalizationAffine

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspProjectiveNormalizationAffine.normalizationAffineIso,
      ``ManuscriptAudit.CuspProjectiveNormalizationAffine.normalizationAffineIso_inv_over] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
