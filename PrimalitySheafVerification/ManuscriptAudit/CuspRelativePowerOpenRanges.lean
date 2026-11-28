import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CuspRelativePowerMap

/-! The actual chart powers preserve the punctured opens. -/

namespace ManuscriptAudit.CuspRelativePowerOpenRanges

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open CuspPunctured (CuspSubalgebra)
open CuspProperCompactification
open CuspProperYChart (lineOpen yOpen lineOpen_range lineOpen_preimage_affine affine_chart_cover)
open CuspRelativePowerCoordinates (cuspPower)
open CuspRelativePowerMap (affineMap lineMap projectiveMap affine_projectiveMap line_projectiveMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K]

private abbrev P := projectiveCusp K
private abbrev L := Spec (CommRingCat.of (Polynomial K))
private abbrev A := affineCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K

private def cuspCube : CuspSubalgebra K :=
  ⟨(Polynomial.X : Polynomial K) ^ 3, Algebra.subset_adjoin (by simp)⟩

private theorem eval_y_over_z :
    affineChartEvaluation K (Away.isLocalizationElem
      (standardPlane_X_mem_one K 2) (standardPlane_X_mem_one K 1)) = cuspCube K := by
  apply Subtype.ext
  unfold Away.isLocalizationElem
  rw [affineChartEvaluation_mk_coe, pow_one]
  simp [cuspCube]

@[reassoc]
private theorem affine_plane :
    affineOpen K ≫ (cuspInPlane K).imageι = cuspInPlane K :=
  Scheme.Hom.toImage_imageι _

/-- The preimage of the line chart in the affine cusp is the actual principal
open of the cube of its normalization parameter. -/
theorem affine_preimage_line :
    (j K) ⁻¹ᵁ (k K).opensRange = PrimeSpectrum.basicOpen (cuspCube K) := by
  rw [lineOpen_range, yOpen, ← Scheme.Hom.comp_preimage, affine_plane, cuspInPlane_as_Z_chart,
    Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := standardPlaneGrading K) (standardPlane_X_mem_one K 2)
      (by decide) (standardPlane_X_mem_one K 1) (by decide), SpecMap_preimage_basicOpen]
  exact congrArg PrimeSpectrum.basicOpen (eval_y_over_z K)

private theorem power_cube (m : ℕ) (hm : 2 ≤ m) :
    cuspPower K m hm (cuspCube K) = (cuspCube K) ^ m := by
  apply Subtype.ext
  change Polynomial.expand K m ((Polynomial.X : Polynomial K) ^ 3) =
    ((Polynomial.X : Polynomial K) ^ 3) ^ m
  rw [map_pow, Polynomial.expand_X, ← pow_mul, ← pow_mul, Nat.mul_comm m 3]

/-- The Laurent open in the infinity chart is invariant under positive powers. -/
theorem power_line_preimage (m : ℕ) (hm : 0 < m) :
    lineMap K m ⁻¹ᵁ (k K ⁻¹ᵁ (j K).opensRange) = k K ⁻¹ᵁ (j K).opensRange := by
  rw [lineOpen_preimage_affine]
  unfold lineMap
  rw [SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (Polynomial.expand K m Polynomial.X) = _
  rw [Polynomial.expand_X, PrimeSpectrum.basicOpen_pow _ _ (Nat.ne_of_gt hm)]

/-- The Laurent open in the cusp chart is likewise invariant. -/
theorem power_affine_preimage (m : ℕ) (hm : 2 ≤ m) :
    affineMap K m hm ⁻¹ᵁ (j K ⁻¹ᵁ (k K).opensRange) = j K ⁻¹ᵁ (k K).opensRange := by
  rw [affine_preimage_line]
  unfold affineMap
  rw [SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (cuspPower K m hm (cuspCube K)) = _
  rw [power_cube, PrimeSpectrum.basicOpen_pow _ _ (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hm))]

end
end ManuscriptAudit.CuspRelativePowerOpenRanges

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspRelativePowerOpenRanges.affine_preimage_line,
      ``ManuscriptAudit.CuspRelativePowerOpenRanges.power_line_preimage,
      ``ManuscriptAudit.CuspRelativePowerOpenRanges.power_affine_preimage] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
