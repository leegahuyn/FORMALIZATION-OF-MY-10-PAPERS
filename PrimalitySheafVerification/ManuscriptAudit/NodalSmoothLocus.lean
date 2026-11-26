import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Noetherian
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineOrigin
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothCharts

/-! The native smooth locus of the proper integral nodal cubic is the
complement of its actual rational conductor point. -/

namespace ManuscriptAudit.NodalSmoothLocus

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspYChartAlgebra (PlaneRing grading y z X_mem_one yChartι)
open CuspProperCompactification (projectivePlaneToBase affineZChartι standardZChartEvaluation_mk)
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase projectiveNode_isProper
  affineNode affineOpen affineOpen_toBase nodeInPlane chartEvaluation chartValues chartValues_Z)
open NodalProperYChart (chartOpen chartOpen_inPlane chartOpen_range yOpen)
open NodalYChartImmersion (yCoordinateRing nodeToYChart nodeYInPlane evalYChart evalYChart_mk)
open NodalConductor (coordinates)
open NodalAffinePresentation (nodeX nodeY)
open NodalAffineOrigin (originPoint originMap originAlgebra originAlgebra_y prime_eq_origin_iff_x_mem)
open NodalSmoothCharts (puncturedAffineAlgebra_smooth yChartAlgebra_smooth projectiveNode_not_smooth)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

instance projectiveNode_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (projectiveNodeToBase K) := by
  letI := projectiveNode_isProper K
  exact (LocallyOfFinitePresentation.iff_locallyOfFiniteType
    (f := projectiveNodeToBase K)).mpr inferInstance

def nodePoint : projectiveNode K := affineOpen K (originPoint K)

private abbrev R := Localization.Away (nodeX K)

private def puncturedAffine : Spec (CommRingCat.of (R K)) ⟶ affineNode K :=
  Spec.map (CommRingCat.ofHom (algebraMap (coordinates K) (R K)))

private instance : IsOpenImmersion (puncturedAffine K) :=
  IsOpenImmersion.of_isLocalization (S := R K) (nodeX K)

def conductorOpen : Spec (CommRingCat.of (R K)) ⟶ projectiveNode K :=
  puncturedAffine K ≫ affineOpen K

instance : IsOpenImmersion (conductorOpen K) := by
  unfold conductorOpen
  infer_instance

private theorem puncturedAffine_range :
    Set.range (puncturedAffine K) =
      (↑(PrimeSpectrum.basicOpen (nodeX K)) : Set (PrimeSpectrum (coordinates K))) :=
  PrimeSpectrum.localization_away_comap_range (R K) (nodeX K)

private theorem conductorOpen_toBase :
    conductorOpen K ≫ projectiveNodeToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (R K))) := by
  unfold conductorOpen puncturedAffine
  rw [Category.assoc, affineOpen_toBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (IsScalarTower.algebraMap_apply K (coordinates K) (R K) a).symm

theorem conductorOpen_smooth : Smooth (conductorOpen K ≫ projectiveNodeToBase K) := by
  rw [conductorOpen_toBase, HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap K (R K)).Smooth
  exact RingHom.smooth_algebraMap.mpr (puncturedAffineAlgebra_smooth K)

private def planeConstants : K →+* grading K 0 where
  toFun a := ⟨MvPolynomial.C a, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_C (Fin 3) a)⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)

theorem chartOpen_toBase :
    chartOpen K ≫ projectiveNodeToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (yCoordinateRing K))) := by
  unfold projectiveNodeToBase
  rw [← Category.assoc, chartOpen_inPlane]
  change nodeToYChart K ≫ yChartι K ≫ Proj.toSpecZero (grading K) ≫
    Spec.map (CommRingCat.ofHom (planeConstants K)) = _
  unfold nodeToYChart yChartι
  simp only [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change evalYChart K (fromZeroRingHom (grading K) _ (planeConstants K a)) = _
  change evalYChart K (Away.mk (grading K) (X_mem_one K 1) 0 (MvPolynomial.C a)
    (by simpa only [zero_nsmul] using
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C (Fin 3) a))) = _
  rw [evalYChart_mk]
  exact MvPolynomial.aeval_C _ _

theorem chartOpen_smooth : Smooth (chartOpen K ≫ projectiveNodeToBase K) := by
  rw [chartOpen_toBase, HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap K (yCoordinateRing K)).Smooth
  exact RingHom.smooth_algebraMap.mpr (yChartAlgebra_smooth K)

private theorem affineOpen_preimage_chartOpen :
    (affineOpen K) ⁻¹ᵁ (chartOpen K).opensRange = PrimeSpectrum.basicOpen (nodeY K) := by
  rw [chartOpen_range]
  unfold yOpen
  rw [← Scheme.Hom.comp_preimage, affineOpen, Scheme.Hom.toImage_imageι, nodeInPlane,
    Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := grading K) (X_mem_one K 2) (by decide)
      (X_mem_one K 1) (by decide), SpecMap_preimage_basicOpen]
  have he : chartEvaluation K (Away.isLocalizationElem (X_mem_one K 2) (X_mem_one K 1)) =
      nodeY K := by
    unfold chartEvaluation Away.isLocalizationElem
    rw [standardZChartEvaluation_mk, pow_one, MvPolynomial.aeval_X]
    simp [chartValues]
  change PrimeSpectrum.basicOpen (chartEvaluation K
      (Away.isLocalizationElem (X_mem_one K 2) (X_mem_one K 1))) = _
  rw [he]

private theorem originPoint_y_mem : nodeY K ∈ (originPoint K).asIdeal := by
  change (originAlgebra K).toRingHom (nodeY K) ∈ (IsLocalRing.closedPoint K).asIdeal
  rw [show (originAlgebra K).toRingHom (nodeY K) = 0 from originAlgebra_y K]
  exact (IsLocalRing.closedPoint K).asIdeal.zero_mem

private theorem nodePoint_not_in_chartOpen : nodePoint K ∉ Set.range (chartOpen K) := by
  intro h
  have hh : originPoint K ∈ (affineOpen K) ⁻¹ᵁ (chartOpen K).opensRange :=
    ((affineOpen K).mem_preimage).mpr h
  rw [affineOpen_preimage_chartOpen] at hh
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hh (originPoint_y_mem K)

private theorem chart_ranges_cover :
    Set.range (affineOpen K) ∪ Set.range (chartOpen K) = Set.univ :=
  congrArg (fun W : (projectiveNode K).Opens => (W : Set (projectiveNode K)))
    (NodalChartIntersection.charts_cover K)

theorem smooth_pieces_cover_complement :
    Set.range (conductorOpen K) ∪ Set.range (chartOpen K) = {nodePoint K}ᶜ := by
  ext p
  change (p ∈ Set.range (conductorOpen K) ∨ p ∈ Set.range (chartOpen K)) ↔ p ≠ nodePoint K
  constructor
  · rintro (⟨q, rfl⟩ | hq)
    · intro h
      have he : puncturedAffine K q = originPoint K :=
        (affineOpen K).isOpenEmbedding.injective h
      have hq : puncturedAffine K q ∈ Set.range (puncturedAffine K) := ⟨q, rfl⟩
      rw [puncturedAffine_range] at hq
      exact (PrimeSpectrum.mem_basicOpen _ _).mp hq
        ((prime_eq_origin_iff_x_mem K _).mp he)
    · intro he
      exact nodePoint_not_in_chartOpen K (he ▸ hq)
  · intro h
    have hc : p ∈ Set.range (affineOpen K) ∪ Set.range (chartOpen K) :=
      (chart_ranges_cover K).symm ▸ Set.mem_univ p
    rcases hc with ⟨q, rfl⟩ | hY
    · left
      have hx : nodeX K ∉ (q : PrimeSpectrum (coordinates K)).asIdeal := by
        intro hx
        exact h (congrArg (affineOpen K) ((prime_eq_origin_iff_x_mem K q).mpr hx))
      have hm : q ∈ Set.range (puncturedAffine K) := by
        rw [puncturedAffine_range]
        exact (PrimeSpectrum.mem_basicOpen _ _).mpr hx
      obtain ⟨t, ht⟩ := hm
      exact ⟨t, congrArg (affineOpen K) ht⟩
    · exact Or.inr hY

private theorem range_subset_smoothLocus {X : Scheme.{u}} (j : X ⟶ projectiveNode K)
    [IsOpenImmersion j] (h : Smooth (j ≫ projectiveNodeToBase K)) :
    Set.range j ⊆ ((projectiveNodeToBase K).smoothLocus : Set (projectiveNode K)) := by
  rintro _ ⟨a, rfl⟩
  letI : Smooth (j ≫ projectiveNodeToBase K) := h
  apply (j.mem_preimage).mp
  rw [j.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- The unique omitted point of the genuine smooth locus is the rational node. -/
theorem smoothLocus_eq_complement :
    ((projectiveNodeToBase K).smoothLocus : Set (projectiveNode K)) = {nodePoint K}ᶜ := by
  have hSub : ({nodePoint K}ᶜ : Set (projectiveNode K)) ⊆ (projectiveNodeToBase K).smoothLocus := by
    rw [← smooth_pieces_cover_complement]
    exact Set.union_subset (range_subset_smoothLocus K _ (conductorOpen_smooth K))
      (range_subset_smoothLocus K _ (chartOpen_smooth K))
  have hBad : nodePoint K ∉ (projectiveNodeToBase K).smoothLocus := by
    intro hp
    apply projectiveNode_not_smooth K
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    apply top_unique
    intro p _
    by_cases hEq : p = nodePoint K
    · exact hEq.symm ▸ hp
    · exact hSub hEq
  refine le_antisymm ?_ hSub
  intro p hp hq
  have hEq : p = nodePoint K := Set.mem_singleton_iff.mp hq
  rw [hEq] at hp
  exact hBad hp

end
end ManuscriptAudit.NodalSmoothLocus

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothLocus.conductorOpen_smooth,
      ``ManuscriptAudit.NodalSmoothLocus.chartOpen_toBase,
      ``ManuscriptAudit.NodalSmoothLocus.chartOpen_smooth,
      ``ManuscriptAudit.NodalSmoothLocus.smooth_pieces_cover_complement,
      ``ManuscriptAudit.NodalSmoothLocus.smoothLocus_eq_complement] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
