import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.FractionRing
import PrimalitySheafVerification.ManuscriptAudit.CuspNormalizedNativeCharts

/-! On the actual normalized proper cusp, the two polynomial
parameter lines meet along the Laurent line, with transition t ↦ t⁻¹. -/

namespace ManuscriptAudit.CuspNormalizedNativeOverlap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (affineOpen)
open CuspProperYChart (lineOpen)
open CuspProjectiveNormalization (normalizationMap)
open CuspNormalizedNativeCharts (affineInclusion lineInclusion affine_isPullback line_over)
open CuspChartIntersection (laurentToAffineLine overlapIsoLaurent)
open CuspChartIntersectionMaps (laurentToAffineCusp laurent_maps_commute
  overlapIsoLaurent_inv_toAffineCusp overlapIsoLaurent_inv_toAffineLine)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

private abbrev B := CommRingCat.of (Polynomial K)
private abbrev L := CommRingCat.of (LaurentPolynomial K)

/-- The normalization's affine coordinate becomes the inverse of the other coordinate. -/
abbrev toAffine : Spec (L K) ⟶ Spec (B K) := CuspYChartImage.laurentToLine K

private theorem toAffine_over :
    toAffine K ≫ CuspScheme.cuspMap K = laurentToAffineCusp K := by
  let u := CommRingCat.ofHom (CuspYChartOverlapAlgebra.lineLaurent K).toRingHom
  let v := CommRingCat.ofHom (LaurentPolynomial.invert (R := K)).toRingHom
  let w := CommRingCat.ofHom (CuspYChartOverlapAlgebra.cuspLaurent K).toRingHom
  change Spec.map u ≫ Spec.map (CuspScheme.inclusion K) = Spec.map v ≫ Spec.map w
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

set_option maxHeartbeats 5400000 in
private theorem cancel_cuspMap_on_laurent {g h : Spec (L K) ⟶ Spec (B K)}
    (e : g ≫ CuspScheme.cuspMap K = h ≫ CuspScheme.cuspMap K) : g = h := by
  let x := Spec.preimage g
  let y := Spec.preimage h
  let F := FractionRing (LaurentPolynomial K)
  let i := algebraMap (LaurentPolynomial K) F
  have ex : CuspScheme.inclusion K ≫ x = CuspScheme.inclusion K ≫ y := by
    apply Spec.map_injective
    simpa only [x, y, Spec.map_comp, Spec.map_preimage, CuspScheme.cuspMap] using e
  have er : i.comp x.hom = i.comp y.hom :=
    (CuspScheme.paper2_cusp_field_ring_points_bijective K F).injective
      (congrArg (fun a : CommRingCat.of (CuspPunctured.CuspSubalgebra K) ⟶ L K ↦
        i.comp a.hom) ex)
  have e' : x = y := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    apply IsFractionRing.injective (LaurentPolynomial K) F
    exact RingHom.congr_fun er b
  exact (Spec.map_preimage g).symm.trans ((congrArg Spec.map e').trans (Spec.map_preimage h))

private theorem outer :
    IsPullback (laurentToAffineCusp K) (laurentToAffineLine K)
      (affineOpen K) (lineInclusion K ≫ normalizationMap K) := by
  rw [line_over]
  let e := overlapIsoLaurent K
  refine (IsPullback.of_hasPullback (affineOpen K) (lineOpen K)).of_iso' e.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
      (overlapIsoLaurent_inv_toAffineCusp K)
  · simpa only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
      (overlapIsoLaurent_inv_toAffineLine K)
  · simp
  · simp

private abbrev right := (affine_isPullback K).flip

private theorem square_commutes :
    laurentToAffineCusp K ≫ affineOpen K =
      (laurentToAffineLine K ≫ lineInclusion K) ≫ normalizationMap K := by
  rw [Category.assoc, line_over]
  exact laurent_maps_commute K

private def liftOverlap : Spec (L K) ⟶ Spec (B K) :=
  (right K).lift (laurentToAffineCusp K)
    (laurentToAffineLine K ≫ lineInclusion K) (square_commutes K)

private theorem lift_eq : liftOverlap K = toAffine K := by
  apply cancel_cuspMap_on_laurent K
  rw [toAffine_over]
  exact (right K).lift_fst _ _ _

/-- With the displayed inverse transition, the Laurent line is exactly the
scheme pullback of the two normalized affine charts. -/
theorem overlap_isPullback :
    IsPullback (toAffine K) (laurentToAffineLine K) (affineInclusion K) (lineInclusion K) := by
  have h : IsPullback (liftOverlap K) (laurentToAffineLine K) (affineInclusion K) (lineInclusion K) :=
    IsPullback.of_right' (outer K) (right K)
  exact (lift_eq K) ▸ h

/-- The two displayed polynomial lines cover the normalized proper cusp. -/
theorem charts_cover :
    (affineInclusion K).opensRange ⊔ (lineInclusion K).opensRange = ⊤ := by
  have h₀ : (affineInclusion K).opensRange = (normalizationMap K) ⁻¹ᵁ (affineOpen K).opensRange := by
    change ((CuspProjectiveNormalizationAffine.normalizationAffineIso K).inv ≫
      pullback.fst (normalizationMap K) (affineOpen K)).opensRange = _
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  have h₁ : (lineInclusion K).opensRange = (normalizationMap K) ⁻¹ᵁ (lineOpen K).opensRange := by
    change ((CuspProjectiveNormalization.normalizationLineIso K).inv ≫
      pullback.fst (normalizationMap K) (lineOpen K)).opensRange = _
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst]
  rw [h₀, h₁]
  apply top_unique
  intro x _
  have hx : normalizationMap K x ∈ (affineOpen K).opensRange ⊔ (lineOpen K).opensRange := by
    rw [CuspProperYChart.affine_chart_cover K]
    trivial
  exact hx

end
end ManuscriptAudit.CuspNormalizedNativeOverlap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNormalizedNativeOverlap.overlap_isPullback,
      ``ManuscriptAudit.CuspNormalizedNativeOverlap.charts_cover] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
