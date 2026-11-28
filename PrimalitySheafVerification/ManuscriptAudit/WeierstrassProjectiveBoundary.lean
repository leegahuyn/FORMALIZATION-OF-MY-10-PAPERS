import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveClosure

/-! The homogeneous equation and the coordinates at infinity of the actual Weierstrass closure. -/

namespace ManuscriptAudit.WeierstrassProjectiveBoundary

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspProperCompactification WeierstrassProjectiveClosure
open scoped Polynomial.Bivariate

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private abbrev P (K : Type u) [Field K] := MvPolynomial (Fin 3) K
private abbrev g (K : Type u) [Field K] := standardPlaneGrading K
private abbrev xCoord (K : Type u) [Field K] : P K := MvPolynomial.X (0 : Fin 3)
private abbrev yCoord (K : Type u) [Field K] : P K := MvPolynomial.X (1 : Fin 3)
private abbrev zCoord (K : Type u) [Field K] : P K := MvPolynomial.X (2 : Fin 3)

private abbrev toZChart : affineScheme W ⟶ Spec (CommRingCat.of (standardZChartRing K)) :=
  Spec.map (CommRingCat.ofHom (chartEvaluation W))

private def homogeneousBracket : P K :=
  yCoord K ^ 2 + MvPolynomial.C W.a₁ * (xCoord K * yCoord K) +
    MvPolynomial.C W.a₃ * (yCoord K * zCoord K) -
    MvPolynomial.C W.a₂ * xCoord K ^ 2 -
    MvPolynomial.C W.a₄ * (xCoord K * zCoord K) - MvPolynomial.C W.a₆ * zCoord K ^ 2

/-- The original homogeneous cubic in the actual projective plane. -/
def homogeneousEquation : P K := homogeneousBracket W * zCoord K - xCoord K ^ 3

theorem homogeneousEquation_degree : MvPolynomial.IsHomogeneous (homogeneousEquation W) 3 := by
  have hx := MvPolynomial.isHomogeneous_X K (0 : Fin 3)
  have hy := MvPolynomial.isHomogeneous_X K (1 : Fin 3)
  have hz := MvPolynomial.isHomogeneous_X K (2 : Fin 3)
  have h : MvPolynomial.IsHomogeneous (homogeneousBracket W) 2 := by
    unfold homogeneousBracket
    exact (((((hy.pow 2).add ((hx.mul hy).C_mul W.a₁)).add
      ((hy.mul hz).C_mul W.a₃)).sub ((hx.pow 2).C_mul W.a₂)).sub
      ((hx.mul hz).C_mul W.a₄)).sub ((hz.pow 2).C_mul W.a₆)
  exact (h.mul hz).sub (hx.pow 3)

private theorem homogeneousEquation_eval :
    MvPolynomial.aeval (chartValues W) (homogeneousEquation W) = 0 := by
  let m := WeierstrassCurve.Affine.CoordinateRing.mk W
  have hX : chartValues W 0 = m (Polynomial.C Polynomial.X) := by simp [chartValues, m]
  have hY : chartValues W 1 = m Y := by simp [chartValues, m]
  have hC (a : K) : algebraMap K W.CoordinateRing a = m (Polynomial.C (Polynomial.C a)) := rfl
  have he : m W.polynomial = 0 := AdjoinRoot.mk_self W.polynomial
  simp only [WeierstrassCurve.Affine.polynomial, map_add, map_mul, map_sub, map_pow] at he
  simp only [homogeneousEquation, homogeneousBracket, xCoord, yCoord, zCoord,
    map_add, map_mul, map_sub, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    hX, hY, hC, chartValues_Z, mul_one, one_pow]
  linear_combination he

private theorem cubic_mem_grade :
    homogeneousEquation W ∈ g K 3 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (homogeneousEquation_degree W)

private theorem inPlane_avoids_cubic_open (p : affineScheme W) :
    inPlane W p ∉ Proj.basicOpen (g K) (homogeneousEquation W) := by
  intro hp
  change toZChart W p ∈ (affineZChartι K) ⁻¹ᵁ
    Proj.basicOpen (g K) (homogeneousEquation W) at hp
  rw [Proj.awayι_preimage_basicOpen (𝒜 := g K) (standardPlane_X_mem_one K 2) (by decide)
    (cubic_mem_grade W) (by decide)] at hp
  have hnot := (PrimeSpectrum.mem_basicOpen _ _).mp hp
  apply hnot
  change chartEvaluation W
    (Away.isLocalizationElem (standardPlane_X_mem_one K 2) (cubic_mem_grade W)) ∈
      (p : PrimeSpectrum (W.CoordinateRing)).asIdeal
  have he : chartEvaluation W
      (Away.isLocalizationElem (standardPlane_X_mem_one K 2) (cubic_mem_grade W)) = 0 := by
    unfold chartEvaluation Away.isLocalizationElem
    rw [standardZChartEvaluation_mk, pow_one, homogeneousEquation_eval]
  rw [he]
  exact (p : PrimeSpectrum (W.CoordinateRing)).asIdeal.zero_mem

private theorem image_range_eq_closure :
    Set.range (inPlane W).imageι = closure (Set.range (inPlane W)) := by
  change Set.range (inPlane W).ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

/-- Every point of the actual proper closure lies on the printed homogeneous cubic. -/
theorem cubic_mem_projective (p : projectiveScheme W) :
    homogeneousEquation W ∈ ((inPlane W).imageι p).asHomogeneousIdeal := by
  classical
  have hSub : closure (Set.range (inPlane W)) ⊆
      ((Proj.basicOpen (g K) (homogeneousEquation W) : Set (projectivePlane K)))ᶜ :=
    closure_minimal (by rintro _ ⟨t, rfl⟩; exact inPlane_avoids_cubic_open W t)
      (Proj.basicOpen (g K) (homogeneousEquation W)).isOpen.isClosed_compl
  have hp : (inPlane W).imageι p ∈ Set.range (inPlane W).imageι := ⟨p, rfl⟩
  rw [image_range_eq_closure W] at hp
  by_contra h
  exact (hSub hp) ((Proj.mem_basicOpen _ _ _).mpr h)

private theorem affineOpen_contains_Z_chart (p : projectiveScheme W)
    (hp : (inPlane W).imageι p ∈ Proj.basicOpen (g K) (zCoord K)) :
    p ∈ Set.range (WeierstrassProjectiveClosure.affineOpen W) := by
  have hi : (inPlane W).imageι p ∈ Set.range (affineZChartι K) := by
    change (inPlane W).imageι p ∈ (affineZChartι K).opensRange
    rw [Proj.opensRange_awayι]
    exact hp
  obtain ⟨q, hq⟩ := hi
  have hqClosure : affineZChartι K q ∈ closure (Set.range (inPlane W)) := by
    rw [hq, ← image_range_eq_closure W]
    exact ⟨p, rfl⟩
  haveI : IsClosedImmersion (toZChart W) :=
    IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective W)
  have hClosed := (toZChart W).isClosedEmbedding.isClosed_range
  have hRange : Set.range (inPlane W) = (affineZChartι K) '' Set.range (toZChart W) := by
    change Set.range ((affineZChartι K) ∘ (toZChart W)) = _
    exact Set.range_comp _ _
  have he := (affineZChartι K).isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
    (Set.range (toZChart W))
  rw [hClosed.closure_eq, ← hRange] at he
  have hqImage : q ∈ Set.range (toZChart W) := by
    rw [he]
    exact hqClosure
  obtain ⟨t, ht⟩ := hqImage
  refine ⟨t, (inPlane W).imageι.isClosedEmbedding.injective ?_⟩
  calc
    _ = inPlane W t := by
      change ((WeierstrassProjectiveClosure.affineOpen W) ≫ (inPlane W).imageι) t = _
      rw [WeierstrassProjectiveClosure.affineOpen, Scheme.Hom.toImage_imageι]
    _ = affineZChartι K q := by
      change affineZChartι K (toZChart W t) = _
      rw [ht]
    _ = _ := hq


/-- All points outside the actual affine chart have X=Z=0 and Y≠0 in the projective plane. -/
theorem boundary_plane_coordinates (p : projectiveScheme W)
    (hp : p ∉ Set.range (WeierstrassProjectiveClosure.affineOpen W)) :
    xCoord K ∈ ((inPlane W).imageι p).asHomogeneousIdeal ∧
      zCoord K ∈ ((inPlane W).imageι p).asHomogeneousIdeal ∧
      yCoord K ∉ ((inPlane W).imageι p).asHomogeneousIdeal := by
  classical
  let q := (inPlane W).imageι p
  let I := q.asHomogeneousIdeal.toIdeal
  have hz : zCoord K ∈ q.asHomogeneousIdeal := by
    by_contra hn
    exact hp (affineOpen_contains_Z_chart W p ((Proj.mem_basicOpen _ _ _).mpr hn))
  have hCube : xCoord K ^ 3 ∈ I := by
    have h := I.sub_mem (I.mul_mem_left (homogeneousBracket W) hz) (cubic_mem_projective W p)
    simpa only [homogeneousEquation, sub_sub_cancel] using h
  have hx : xCoord K ∈ q.asHomogeneousIdeal := q.isPrime.mem_of_pow_mem 3 hCube
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

end ManuscriptAudit.WeierstrassProjectiveBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveBoundary.homogeneousEquation_degree,
      ``ManuscriptAudit.WeierstrassProjectiveBoundary.cubic_mem_projective,
      ``ManuscriptAudit.WeierstrassProjectiveBoundary.boundary_plane_coordinates] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
