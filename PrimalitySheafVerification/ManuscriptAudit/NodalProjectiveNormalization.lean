import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Normalization
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusOverlap

/-! The native projective relative normalization of the split node and
its actual pullback over the smooth Y-chart. -/

namespace ManuscriptAudit.NodalProjectiveNormalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase projectiveNode_isProper)
open NodalSmoothLocusOverlap (smoothOpen smoothScheme zSmooth ySmooth ySmooth_ambient
  smooth_charts_cover puncturedZ puncturedZRing)
open NodalYChartImmersion (nodeYChart yCoordinateRing)
open NodalProperYChart (chartOpen)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

private instance smoothScheme_compactSpace : CompactSpace (smoothScheme K) := by
  letI : CompactSpace (puncturedZ K) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum (puncturedZRing K)))
  letI : CompactSpace (nodeYChart K) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum (yCoordinateRing K)))
  apply isCompact_univ_iff.mp
  rw [← smooth_charts_cover K]
  exact (isCompact_range (zSmooth K).continuous).union (isCompact_range (ySmooth K).continuous)

abbrev smoothInclusion : smoothScheme K ⟶ projectiveNode K := (smoothOpen K).ι

instance smoothInclusion_quasiCompact : QuasiCompact (smoothInclusion K) := by
  letI : IsProper (projectiveNodeToBase K) := projectiveNode_isProper K
  letI : QuasiSeparatedSpace (projectiveNode K) :=
    quasiSeparatedSpace_of_quasiSeparated (projectiveNodeToBase K)
  exact quasiCompact_of_compactSpace (smoothInclusion K)

abbrev normalizedNode : Scheme.{u} := (smoothInclusion K).normalization

def normalizationMap : normalizedNode K ⟶ projectiveNode K :=
  (smoothInclusion K).fromNormalization

theorem normalizationMap_integral : IsIntegralHom (normalizationMap K) :=
  inferInstanceAs (IsIntegralHom (smoothInclusion K).fromNormalization)

theorem inclusion_factors :
    (smoothInclusion K).toNormalization ≫ normalizationMap K = smoothInclusion K :=
  (smoothInclusion K).toNormalization_fromNormalization

private instance baseChangeSmoothInclusion_iso :
    IsIso (pullback.snd (smoothInclusion K) (chartOpen K)) := by
  let p := pullback.snd (smoothInclusion K) (chartOpen K)
  have h : ySmooth K ≫ smoothInclusion K = 𝟙 (nodeYChart K) ≫ chartOpen K := by
    rw [Category.id_comp]
    exact ySmooth_ambient K
  let i : nodeYChart K ⟶ pullback (smoothInclusion K) (chartOpen K) :=
    pullback.lift (ySmooth K) (𝟙 _) h
  have hi : i ≫ p = 𝟙 _ := by simp [i, p]
  refine ⟨⟨i, ?_, hi⟩⟩
  apply (cancel_mono p).mp
  rw [Category.assoc, hi, Category.comp_id, Category.id_comp]

/-- The normalization changes nothing over the actual smooth Y-chart. -/
theorem normalizationMap_pullback_Y_iso :
    IsIso (pullback.snd (normalizationMap K) (chartOpen K)) := by
  let f := smoothInclusion K
  let g := chartOpen K
  let p := pullback.snd f g
  haveI : IsIso p := baseChangeSmoothInclusion_iso K
  haveI : IsIso p.toNormalization := inferInstance
  have h : p.fromNormalization = inv p.toNormalization ≫ p :=
    (IsIso.eq_inv_comp p.toNormalization).mpr p.toNormalization_fromNormalization
  haveI : IsIso p.fromNormalization := h.symm ▸ inferInstanceAs
    (IsIso (inv p.toNormalization ≫ p))
  haveI : Smooth g := inferInstance
  haveI : IsIso (f.normalizationPullback g) := inferInstance
  have h' : pullback.snd f.fromNormalization g = inv (f.normalizationPullback g) ≫
      p.fromNormalization :=
    (IsIso.eq_inv_comp (f.normalizationPullback g)).mpr (f.normalizationPullback_snd g)
  change IsIso (pullback.snd f.fromNormalization g)
  rw [h']
  infer_instance

/-- The entire normalization over the Y-chart is the original Y-chart. -/
def normalizationYChartIso :
    pullback (normalizationMap K) (chartOpen K) ≅ nodeYChart K := by
  letI := normalizationMap_pullback_Y_iso K
  exact asIso (pullback.snd (normalizationMap K) (chartOpen K))

end
end ManuscriptAudit.NodalProjectiveNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveNormalization.normalizationMap_integral,
      ``ManuscriptAudit.NodalProjectiveNormalization.inclusion_factors,
      ``ManuscriptAudit.NodalProjectiveNormalization.normalizationMap_pullback_Y_iso,
      ``ManuscriptAudit.NodalProjectiveNormalization.normalizationYChartIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
