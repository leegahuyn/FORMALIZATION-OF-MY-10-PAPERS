import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import PrimalitySheafVerification.ManuscriptAudit.CuspNormalizedNativeOverlap
import PrimalitySheafVerification.ManuscriptAudit.CuspProperNormalizationHomeomorphism

/-! The actual normalization of the proper cusp is smooth and proper
over the original coefficient field, in every characteristic. -/

namespace ManuscriptAudit.CuspNormalizedSmoothProper

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open CuspProperCompactification (projectiveCuspToBase projectiveCusp_isProper
  projectivePlaneToBase cuspInPlane affineOpen affineOpen_toBase)
open CuspProperYChart (lineOpen lineOpen_inPlane)
open CuspYChartAlgebra (lineInPlane evalYChart evalYChart_mk evalYPolynomial grading X_mem_one)
open CuspProjectiveNormalization (normalizedCusp normalizationMap)
open CuspNormalizedNativeCharts (affineInclusion lineInclusion affine_isPullback line_over)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

/-- Structure morphism of the true normalized proper cusp. -/
abbrev toBase : normalizedCusp K ⟶ Spec (CommRingCat.of K) :=
  normalizationMap K ≫ projectiveCuspToBase K

theorem proper : IsProper (toBase K) := by
  letI := CuspProperNormalizationHomeomorphism.finite K
  letI := projectiveCusp_isProper K
  infer_instance

private abbrev B := Spec (CommRingCat.of (Polynomial K))
private abbrev polynomialToBase := Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))

set_option maxHeartbeats 5000000 in
private theorem line_structure : lineOpen K ≫ projectiveCuspToBase K = polynomialToBase K := by
  change lineOpen K ≫ ((cuspInPlane K).imageι ≫ projectivePlaneToBase K) = _
  rw [← Category.assoc, lineOpen_inPlane]
  change (Spec.map (CommRingCat.ofHom (evalYChart K)) ≫
      Proj.awayι (grading K) (CuspYChartAlgebra.y K) (X_mem_one K 1) (by decide)) ≫
    (Proj.toSpecZero (grading K) ≫ Spec.map _) = _
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  have ha : (MvPolynomial.C a : CuspYChartAlgebra.PlaneRing K) ∈ grading K 0 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C (Fin 3) a)
  change evalYChart K (Away.mk (grading K) (X_mem_one K 1) 0 (MvPolynomial.C a)
    (by simpa only [zero_nsmul] using ha)) = algebraMap K (Polynomial K) a
  rw [evalYChart_mk]
  exact (evalYPolynomial K).commutes a

private theorem affine_structure : affineInclusion K ≫ toBase K = polynomialToBase K := by
  change affineInclusion K ≫ normalizationMap K ≫ projectiveCuspToBase K = _
  rw [← Category.assoc, (affine_isPullback K).w, Category.assoc, affineOpen_toBase]
  change Spec.map (CuspScheme.inclusion K) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

private def chartInclusion : Bool → (B K ⟶ normalizedCusp K)
  | false => affineInclusion K
  | true => lineInclusion K

private def cover : (normalizedCusp K).OpenCover where
  I₀ := Bool
  X _ := B K
  f := chartInclusion K
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · have h : Set.range (affineInclusion K) ∪ Set.range (lineInclusion K) = Set.univ :=
        congrArg (fun U : (normalizedCusp K).Opens ↦ (U : Set (normalizedCusp K)))
          (CuspNormalizedNativeOverlap.charts_cover K)
      intro x
      have hx : x ∈ Set.range (affineInclusion K) ∪ Set.range (lineInclusion K) :=
        h.symm ▸ Set.mem_univ x
      rcases hx with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨false, a, ha⟩
      · exact ⟨true, b, hb⟩
    · intro i
      cases i
      · exact inferInstanceAs (IsOpenImmersion (affineInclusion K))
      · exact inferInstanceAs (IsOpenImmersion (lineInclusion K))

private theorem polynomial_smooth : Smooth (polynomialToBase K) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr (show Algebra.Smooth K (Polynomial K) from {})

set_option maxHeartbeats 5000000 in
theorem smooth : Smooth (toBase K) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) (cover K)]
  intro i
  cases i
  · change Smooth (affineInclusion K ≫ toBase K)
    rw [affine_structure]
    exact polynomial_smooth K
  · change Smooth (lineInclusion K ≫ normalizationMap K ≫ projectiveCuspToBase K)
    rw [← Category.assoc, line_over, line_structure]
    exact polynomial_smooth K

end
end ManuscriptAudit.CuspNormalizedSmoothProper

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNormalizedSmoothProper.proper,
      ``ManuscriptAudit.CuspNormalizedSmoothProper.smooth] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
