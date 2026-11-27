import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveNormalization

/-! The normalization over the Z-chart reduces to the native relative
normalization of the actual conductor localization of the affine node. -/

namespace ManuscriptAudit.NodalNormalizationZChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (affineOpen affineNode projectiveNodeToBase)
open NodalSmoothLocus (smoothLocus_eq_complement nodePoint)
open NodalSmoothLocusOverlap (smoothOpen puncturedZ puncturedZRing puncturedZ_toAffine
  zSmooth zSmooth_ambient conductorOpen_factors)
open NodalProjectiveNormalization (smoothInclusion normalizationMap)
open NodalAffinePresentation (nodeX)
open NodalAffineOrigin (originPoint prime_eq_origin_iff_x_mem)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

private theorem preimage_smoothOpen :
    (affineOpen K) ⁻¹ᵁ smoothOpen K = PrimeSpectrum.basicOpen (nodeX K) := by
  ext p
  change affineOpen K p ∈ ((projectiveNodeToBase K).smoothLocus : Set _) ↔
    p ∈ PrimeSpectrum.basicOpen (nodeX K)
  rw [smoothLocus_eq_complement, Set.mem_compl_iff, Set.mem_singleton_iff,
    PrimeSpectrum.mem_basicOpen]
  change affineOpen K p ≠ affineOpen K (originPoint K) ↔ nodeX K ∉ p.asIdeal
  exact not_congr ((affineOpen K).isOpenEmbedding.injective.eq_iff.trans
    (prime_eq_origin_iff_x_mem K p))

private theorem pullback_snd_range :
    Set.range (pullback.snd (smoothInclusion K) (affineOpen K)) =
      Set.range (puncturedZ_toAffine K) := by
  have h : (smoothInclusion K).opensRange = smoothOpen K := by
    apply SetLike.coe_injective
    exact Scheme.Opens.range_ι _
  have h' : (pullback.snd (smoothInclusion K) (affineOpen K)).opensRange =
      PrimeSpectrum.basicOpen (nodeX K) := by
    rw [Scheme.Hom.opensRange_pullbackSnd, h, preimage_smoothOpen]
  calc
    _ = (PrimeSpectrum.basicOpen (nodeX K)).1 :=
      congrArg (fun V : (affineNode K).Opens => (V : Set (affineNode K))) h'
    _ = _ := (PrimeSpectrum.localization_away_comap_range (puncturedZRing K) (nodeX K)).symm

/-- The actual Z-chart pullback of the smooth open is its conductor puncture. -/
def smoothZChartIso :
    puncturedZ K ≅ pullback (smoothInclusion K) (affineOpen K) :=
  IsOpenImmersion.isoOfRangeEq (puncturedZ_toAffine K)
    (pullback.snd (smoothInclusion K) (affineOpen K)) (pullback_snd_range K).symm

theorem smoothZChartIso_snd :
    (smoothZChartIso K).hom ≫ pullback.snd (smoothInclusion K) (affineOpen K) =
      puncturedZ_toAffine K :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem smoothZChartIso_fst :
    (smoothZChartIso K).hom ≫ pullback.fst (smoothInclusion K) (affineOpen K) =
      zSmooth K := by
  apply (cancel_mono (smoothInclusion K)).mp
  rw [Category.assoc, pullback.condition, ← Category.assoc, smoothZChartIso_snd,
    zSmooth_ambient, conductorOpen_factors]

/-- Actual smooth base change identifies the normalization over Z with the
relative normalization of its pullback inclusion. -/
def relativeNormalizationZIso :
    (pullback.snd (smoothInclusion K) (affineOpen K)).normalization ≅
      pullback (normalizationMap K) (affineOpen K) :=
  asIso ((smoothInclusion K).normalizationPullback (affineOpen K))

/-- The pullback normalization over Z is the relative normalization
of the native affine localization map. -/
def punctureNormalizationZIso :
    (puncturedZ_toAffine K).normalization ≅ pullback (normalizationMap K) (affineOpen K) := by
  let f := puncturedZ_toAffine K
  let g := pullback.snd (smoothInclusion K) (affineOpen K)
  let e := smoothZChartIso K
  have hf : f = e.hom ≫ g := (smoothZChartIso_snd K).symm
  have hg : g = e.inv ≫ f := by rw [hf, Iso.inv_hom_id_assoc]
  let u := f.normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]; exact hf)
  let v := g.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]; exact hg)
  let E : f.normalization ≅ g.normalization :=
    { hom := u
      inv := v
      hom_inv_id := by
        apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
        · simp [u, v, Category.assoc]
        · simp [u, v, Category.assoc]
        · simp
      inv_hom_id := by
        apply Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
        · simp [u, v, Category.assoc]
        · simp [u, v, Category.assoc]
        · simp }
  exact E ≪≫ relativeNormalizationZIso K

/-- The comparison remains over the actual affine Z chart. -/
theorem punctureNormalizationZIso_hom_snd :
    (punctureNormalizationZIso K).hom ≫ pullback.snd (normalizationMap K) (affineOpen K) =
      (puncturedZ_toAffine K).fromNormalization := by
  simp only [punctureNormalizationZIso, relativeNormalizationZIso, Iso.trans_hom, asIso_hom,
    Category.assoc, normalizationMap, Scheme.Hom.normalizationPullback_snd,
    Scheme.Hom.normalizationDesc_comp]

end
end ManuscriptAudit.NodalNormalizationZChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizationZChart.smoothZChartIso_snd,
      ``ManuscriptAudit.NodalNormalizationZChart.smoothZChartIso_fst,
      ``ManuscriptAudit.NodalNormalizationZChart.relativeNormalizationZIso,
      ``ManuscriptAudit.NodalNormalizationZChart.punctureNormalizationZIso,
      ``ManuscriptAudit.NodalNormalizationZChart.punctureNormalizationZIso_hom_snd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
