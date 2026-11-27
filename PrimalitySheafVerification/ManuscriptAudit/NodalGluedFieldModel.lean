import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalGluedFieldCharts
import PrimalitySheafVerification.ManuscriptAudit.NodalPlaneChartBase

/-! The scheme obtained by the literal integral gluing recipe, over a field,
is the already-constructed proper projective node. -/

namespace ManuscriptAudit.NodalGluedFieldModel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralGluing
open NodalGluedFieldCharts
open NodalChartIntersection (charts_cover intersectionIsoParameter
  intersectionIsoParameter_inv_fst intersectionIsoParameter_inv_snd)
open NodalProjectiveClosure (affineNode projectiveNode affineOpen projectiveNodeToBase)
open NodalProperYChart (chartOpen)
open NodalYChartImmersion (nodeYChart)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

private def targetChart : Bool → Scheme.{u}
  | false => affineNode K
  | true => nodeYChart K

private def targetChartIn : ∀ b : Bool, targetChart K b ⟶ projectiveNode K
  | false => affineOpen K
  | true => chartOpen K

private instance (b : Bool) : IsOpenImmersion (targetChartIn K b) := by
  cases b
  · exact inferInstanceAs (IsOpenImmersion (affineOpen K))
  · exact inferInstanceAs (IsOpenImmersion (chartOpen K))

private def cover : (projectiveNode K).OpenCover where
  I₀ := Bool
  X := targetChart K
  f := targetChartIn K
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro p
    have h : p ∈ (affineOpen K).opensRange ⊔ (chartOpen K).opensRange := by
      rw [charts_cover]
      trivial
    change p ∈ Set.range (affineOpen K) ∨ p ∈ Set.range (chartOpen K) at h
    rcases h with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact ⟨false, q, hq⟩
    · exact ⟨true, q, hq⟩

private def chartIso : ∀ b : Bool, chartObj K b ≅ targetChart K b
  | false => zSchemeIso K
  | true => ySchemeIso K

private def chartMap (b : Bool) : chartObj K b ⟶ projectiveNode K :=
  (chartIso K b).hom ≫ targetChartIn K b

private theorem chartMap_compat :
    overlapToZ K ≫ chartMap K false = overlapToY K ≫ chartMap K true := by
  apply (cancel_epi (overlapSchemeIso K).hom).mp
  change (overlapSchemeIso K).hom ≫ overlapToZ K ≫ (zSchemeIso K).hom ≫ affineOpen K =
    (overlapSchemeIso K).hom ≫ overlapToY K ≫ (ySchemeIso K).hom ≫ chartOpen K
  rw [overlapSchemeIso_toZ_assoc, overlapSchemeIso_toY_assoc]
  rw [← NodalChartIntersection.intersectionIsoParameter_inv_fst_assoc,
    ← NodalChartIntersection.intersectionIsoParameter_inv_snd_assoc, pullback.condition]

private def modelCocone : Cocone (diagram K) :=
  WidePushoutShape.mkCocone (overlapToZ K ≫ chartMap K false) (chartMap K) (by
    intro b
    cases b
    · rfl
    · exact (chartMap_compat K).symm)

private def toProper : model K ⟶ projectiveNode K :=
  colimit.desc (diagram K) (modelCocone K)

private theorem chartIn_toProper (b : Bool) :
    chartIn K b ≫ toProper K = chartMap K b :=
  colimit.ι_desc (modelCocone K) (some b)

private def inverseChartMap (b : Bool) : (cover K).X b ⟶ model K :=
  (chartIso K b).inv ≫ chartIn K b

private theorem inverseChartMap_compat_forward :
    pullback.fst ((cover K).f false) ((cover K).f true) ≫ inverseChartMap K false =
    pullback.snd _ _ ≫ inverseChartMap K true := by
  apply (cancel_epi (intersectionIsoParameter K).inv).mp
  change (intersectionIsoParameter K).inv ≫ pullback.fst (affineOpen K) (chartOpen K) ≫
      (zSchemeIso K).inv ≫ chartIn K false =
    (intersectionIsoParameter K).inv ≫ pullback.snd (affineOpen K) (chartOpen K) ≫
      (ySchemeIso K).inv ≫ chartIn K true
  rw [NodalChartIntersection.intersectionIsoParameter_inv_fst_assoc,
    NodalChartIntersection.intersectionIsoParameter_inv_snd_assoc,
    ← overlapSchemeIso_toZ_assoc, ← overlapSchemeIso_toY_assoc]
  simp only [Iso.hom_inv_id_assoc]
  have hZ : overlapToZ K ≫ chartIn K false = colimit.ι (diagram K) none :=
    colimit.w (diagram K) (WidePushoutShape.Hom.init false)
  have hY : overlapToY K ≫ chartIn K true = colimit.ι (diagram K) none :=
    colimit.w (diagram K) (WidePushoutShape.Hom.init true)
  rw [hZ, hY]

private theorem inverseChartMap_compat (a b : Bool) :
    pullback.fst ((cover K).f a) ((cover K).f b) ≫ inverseChartMap K a =
    pullback.snd _ _ ≫ inverseChartMap K b := by
  cases a <;> cases b
  · have h : pullback.fst ((cover K).f false) ((cover K).f false) =
        pullback.snd ((cover K).f false) ((cover K).f false) :=
      (cancel_mono ((cover K).f false)).mp pullback.condition
    rw [h]
  · exact inverseChartMap_compat_forward K
  · apply (cancel_epi (pullbackSymmetry ((cover K).f false) ((cover K).f true)).hom).mp
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
    exact (inverseChartMap_compat_forward K).symm
  · have h : pullback.fst ((cover K).f true) ((cover K).f true) =
        pullback.snd ((cover K).f true) ((cover K).f true) :=
      (cancel_mono ((cover K).f true)).mp pullback.condition
    rw [h]

private def fromProper : projectiveNode K ⟶ model K :=
  (cover K).glueMorphisms (inverseChartMap K) (inverseChartMap_compat K)

private theorem chartIn_fromProper (b : Bool) :
    (cover K).f b ≫ fromProper K = inverseChartMap K b :=
  (cover K).ι_glueMorphisms _ _ b

private theorem chartIn_toProper_fromProper (b : Bool) :
    chartIn K b ≫ toProper K ≫ fromProper K = chartIn K b := by
  rw [← Category.assoc, chartIn_toProper]
  change ((chartIso K b).hom ≫ (cover K).f b) ≫ fromProper K = _
  rw [Category.assoc, chartIn_fromProper]
  simp [inverseChartMap]

/-- The literal two-chart nodal model over a field is the actual proper cubic. -/
def modelIso : model K ≅ projectiveNode K where
  hom := toProper K
  inv := fromProper K
  hom_inv_id := by
    apply colimit.hom_ext
    intro i
    simp only [Category.comp_id]
    cases i with
    | some b => exact chartIn_toProper_fromProper K b
    | none =>
      have hZ : overlapToZ K ≫ chartIn K false = colimit.ι (diagram K) none :=
        colimit.w (diagram K) (WidePushoutShape.Hom.init false)
      change colimit.ι (diagram K) none ≫ toProper K ≫ fromProper K = _
      rw [← hZ, Category.assoc, chartIn_toProper_fromProper]
  inv_hom_id := by
    apply (cover K).hom_ext
    intro b
    change (cover K).f b ≫ (fromProper K ≫ toProper K) = (cover K).f b ≫ 𝟙 _
    rw [← Category.assoc, chartIn_fromProper]
    change ((chartIso K b).inv ≫ chartIn K b) ≫ toProper K = _
    rw [Category.assoc, chartIn_toProper]
    change (chartIso K b).inv ≫ ((chartIso K b).hom ≫ (cover K).f b) = _
    simp


private theorem zSchemeIso_base :
    (zSchemeIso K).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (NodalConductor.coordinates K))) =
      chartToBase K false := by
  change Spec.map (CommRingCat.ofHom (zChartEquiv K).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (NodalConductor.coordinates K))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (zChartEquiv K).symm.commutes

private theorem ySchemeIso_base :
    (ySchemeIso K).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (NodalYChartImmersion.yCoordinateRing K))) =
      chartToBase K true := by
  change Spec.map (CommRingCat.ofHom (yChartEquiv K).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (NodalYChartImmersion.yCoordinateRing K))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (yChartEquiv K).symm.commutes

private theorem yChart_over :
    chartOpen K ≫ projectiveNodeToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (NodalYChartImmersion.yCoordinateRing K))) := by
  unfold projectiveNodeToBase
  rw [← Category.assoc, NodalProperYChart.chartOpen_inPlane]
  unfold NodalYChartImmersion.nodeYInPlane NodalYChartImmersion.nodeToYChart
  rw [Category.assoc]
  apply NodalPlaneChartBase.standardPlaneChartPoint_toBase K 1
  intro a
  rw [NodalYChartImmersion.evalYChart_mk]
  simp [NodalYChartImmersion.evalYPolynomial]

private theorem chartMap_over (b : Bool) :
    chartMap K b ≫ projectiveNodeToBase K = chartToBase K b := by
  cases b
  · change ((zSchemeIso K).hom ≫ affineOpen K) ≫ projectiveNodeToBase K = _
    rw [Category.assoc, NodalProjectiveClosure.affineOpen_toBase, zSchemeIso_base]
  · change ((ySchemeIso K).hom ≫ chartOpen K) ≫ projectiveNodeToBase K = _
    rw [Category.assoc, yChart_over, ySchemeIso_base]

/-- The model identification preserves the morphisms to the coefficient field. -/
theorem modelIso_over :
    (modelIso K).hom ≫ projectiveNodeToBase K = toBase K := by
  change toProper K ≫ projectiveNodeToBase K = _
  apply colimit.hom_ext
  intro i
  cases i with
  | some b =>
    change chartIn K b ≫ toProper K ≫ projectiveNodeToBase K =
      chartIn K b ≫ toBase K
    rw [← Category.assoc, chartIn_toProper, chartMap_over, chartIn_over]
  | none =>
    have hZ : overlapToZ K ≫ chartIn K false = colimit.ι (diagram K) none :=
      colimit.w (diagram K) (WidePushoutShape.Hom.init false)
    rw [← hZ]
    simp only [Category.assoc]
    suffices h : chartIn K false ≫ toProper K ≫ projectiveNodeToBase K =
        chartIn K false ≫ toBase K by rw [h]
    rw [← Category.assoc, chartIn_toProper, chartMap_over, chartIn_over]

end
end ManuscriptAudit.NodalGluedFieldModel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalGluedFieldModel.modelIso,
      ``ManuscriptAudit.NodalGluedFieldModel.modelIso_over] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
