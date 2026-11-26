import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveClosure

/-! The actual proper nodal closure satisfies the homogeneous equation. -/

namespace ManuscriptAudit.NodalProjectiveBoundary

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspProperCompactification NodalProjectiveClosure

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

private abbrev P := MvPolynomial (Fin 3) K
private abbrev g := standardPlaneGrading K
private abbrev xCoord : P K := MvPolynomial.X (0 : Fin 3)
private abbrev yCoord : P K := MvPolynomial.X (1 : Fin 3)
private abbrev zCoord : P K := MvPolynomial.X (2 : Fin 3)
private abbrev nodalOpen := NodalProjectiveClosure.affineOpen K

private abbrev nodeToZChart : affineNode K ⟶ Spec (CommRingCat.of (standardZChartRing K)) :=
  Spec.map (CommRingCat.ofHom (chartEvaluation K))

private theorem cubic_mem_grade :
    homogeneousEquation K ∈ g K 3 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (homogeneousEquation_degree K)

private theorem nodeInPlane_avoids_cubic_open (p : affineNode K) :
    nodeInPlane K p ∉ Proj.basicOpen (g K) (homogeneousEquation K) := by
  intro hp
  change nodeToZChart K p ∈ (affineZChartι K) ⁻¹ᵁ
    Proj.basicOpen (g K) (homogeneousEquation K) at hp
  rw [Proj.awayι_preimage_basicOpen (𝒜 := g K) (standardPlane_X_mem_one K 2) (by decide)
    (cubic_mem_grade K) (by decide)] at hp
  have hnot := (PrimeSpectrum.mem_basicOpen _ _).mp hp
  apply hnot
  change chartEvaluation K
    (Away.isLocalizationElem (standardPlane_X_mem_one K 2) (cubic_mem_grade K)) ∈
      (p : PrimeSpectrum (NodalConductor.coordinates K)).asIdeal
  have he : chartEvaluation K
      (Away.isLocalizationElem (standardPlane_X_mem_one K 2) (cubic_mem_grade K)) = 0 := by
    unfold chartEvaluation Away.isLocalizationElem
    rw [standardZChartEvaluation_mk, pow_one, homogeneousEquation_eval]
  rw [he]
  exact (p : PrimeSpectrum (NodalConductor.coordinates K)).asIdeal.zero_mem

private theorem image_range_eq_closure :
    Set.range (nodeInPlane K).imageι = closure (Set.range (nodeInPlane K)) := by
  change Set.range (nodeInPlane K).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

/-- Every point of the actual proper closure lies on the printed homogeneous cubic. -/
theorem cubic_mem_projectiveNode (p : projectiveNode K) :
    homogeneousEquation K ∈ ((nodeInPlane K).imageι p).asHomogeneousIdeal := by
  classical
  have hSub : closure (Set.range (nodeInPlane K)) ⊆
      ((Proj.basicOpen (g K) (homogeneousEquation K) : Set (projectivePlane K)))ᶜ :=
    closure_minimal (by rintro _ ⟨t, rfl⟩; exact nodeInPlane_avoids_cubic_open K t)
      (Proj.basicOpen (g K) (homogeneousEquation K)).isOpen.isClosed_compl
  have hp : (nodeInPlane K).imageι p ∈ Set.range (nodeInPlane K).imageι := ⟨p, rfl⟩
  rw [image_range_eq_closure] at hp
  by_contra h
  exact (hSub hp) ((Proj.mem_basicOpen _ _ _).mpr h)

private theorem affineOpen_contains_Z_chart (p : projectiveNode K)
    (hp : (nodeInPlane K).imageι p ∈ Proj.basicOpen (g K) (zCoord K)) :
    p ∈ Set.range (nodalOpen K) := by
  have hi : (nodeInPlane K).imageι p ∈ Set.range (affineZChartι K) := by
    change (nodeInPlane K).imageι p ∈ (affineZChartι K).opensRange
    rw [Proj.opensRange_awayι]
    exact hp
  obtain ⟨q, hq⟩ := hi
  have hqClosure : affineZChartι K q ∈ closure (Set.range (nodeInPlane K)) := by
    rw [hq, ← image_range_eq_closure]
    exact ⟨p, rfl⟩
  haveI : IsClosedImmersion (nodeToZChart K) :=
    IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective K)
  have hClosed := (nodeToZChart K).isClosedEmbedding.isClosed_range
  have hRange : Set.range (nodeInPlane K) = (affineZChartι K) '' Set.range (nodeToZChart K) := by
    change Set.range ((affineZChartι K) ∘ (nodeToZChart K)) = _
    exact Set.range_comp _ _
  have he := (affineZChartι K).isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
    (Set.range (nodeToZChart K))
  rw [hClosed.closure_eq, ← hRange] at he
  have hqImage : q ∈ Set.range (nodeToZChart K) := by
    rw [he]
    exact hqClosure
  obtain ⟨t, ht⟩ := hqImage
  refine ⟨t, (nodeInPlane K).imageι.isClosedEmbedding.injective ?_⟩
  calc
    _ = nodeInPlane K t := by
      change ((NodalProjectiveClosure.affineOpen K) ≫ (nodeInPlane K).imageι) t = _
      rw [NodalProjectiveClosure.affineOpen, Scheme.Hom.toImage_imageι]
    _ = affineZChartι K q := by
      change affineZChartι K (nodeToZChart K t) = _
      rw [ht]
    _ = _ := hq

/-- At every boundary point the actual image coordinates have X=Z=0 and Y≠0. -/
theorem boundary_plane_coordinates (p : projectiveNode K)
    (hp : p ∉ Set.range (nodalOpen K)) :
    xCoord K ∈ ((nodeInPlane K).imageι p).asHomogeneousIdeal ∧
      zCoord K ∈ ((nodeInPlane K).imageι p).asHomogeneousIdeal ∧
      yCoord K ∉ ((nodeInPlane K).imageι p).asHomogeneousIdeal := by
  classical
  let q := (nodeInPlane K).imageι p
  let I := q.asHomogeneousIdeal.toIdeal
  have hz : zCoord K ∈ q.asHomogeneousIdeal := by
    by_contra hn
    exact hp (affineOpen_contains_Z_chart K p ((Proj.mem_basicOpen _ _ _).mpr hn))
  have hCube : xCoord K ^ 3 ∈ I := by
    have he : xCoord K ^ 3 =
        (yCoord K ^ 2 * zCoord K - homogeneousEquation K) - xCoord K ^ 2 * zCoord K := by
      unfold homogeneousEquation
      ring
    rw [he]
    exact I.sub_mem
      (I.sub_mem (I.mul_mem_left (yCoord K ^ 2) hz) (cubic_mem_projectiveNode K p))
      (I.mul_mem_left (xCoord K ^ 2) hz)
  have hx : xCoord K ∈ q.asHomogeneousIdeal :=
    q.isPrime.mem_of_pow_mem 3 hCube
  have hTop : q ∈ (⊤ : (projectivePlane K).Opens) := trivial
  rw [← standardPlane_basicOpens_cover K] at hTop
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hTop
  have hni := (Proj.mem_basicOpen _ _ _).mp hi
  refine ⟨hx, hz, ?_⟩
  fin_cases i
  · exact (hni hx).elim
  · exact hni
  · exact (hni hz).elim

end
end ManuscriptAudit.NodalProjectiveBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveBoundary.cubic_mem_projectiveNode,
      ``ManuscriptAudit.NodalProjectiveBoundary.boundary_plane_coordinates] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
