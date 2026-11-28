import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspRelativePowerCartesian
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothHOne

/-! Relative power preserves the genuine regular open of the proper cusp. -/

namespace ManuscriptAudit.CuspRelativePowerSmoothOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspPunctured (cuspSquare)
open CuspNativeCompactSmoothHOne (smoothOpen)
open SmallEtaleGeometricBaseChange (cuspPuncturedOpen)
open CuspRelativePowerOpenRanges (affine_preimage_line_square)
open CuspRelativePowerCartesian (overlapInclusion overlap_preimage)
open CuspRelativePowerMap (projectiveMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev s := smoothOpen K

/-- The literal smooth open has the same range as the actual chart overlap. -/
theorem smooth_range :
    (s K).opensRange = (overlapInclusion K).opensRange := by
  have hL : (s K).opensRange = (j K).opensRange ⊓ (k K).opensRange := by
    change ((cuspPuncturedOpen K).ι ≫ j K).opensRange = _
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    change (j K) ''ᵁ PrimeSpectrum.basicOpen (cuspSquare K) = _
    rw [← affine_preimage_line_square, Scheme.Hom.image_preimage_eq_opensRange_inf]
  have hR : (overlapInclusion K).opensRange = (j K).opensRange ⊓ (k K).opensRange := by
    rw [overlapInclusion, Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_pullbackFst,
      Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact hL.trans hR.symm

variable (m : ℕ) (hm : 2 ≤ m)

private abbrev f := projectiveMap K m hm

theorem smooth_preimage :
    f K m hm ⁻¹ᵁ (s K).opensRange = (s K).opensRange := by
  rw [smooth_range]
  exact overlap_preimage K m hm

private theorem smooth_image :
    Set.range (s K ≫ f K m hm) ⊆ Set.range (s K) := by
  rintro x ⟨a, rfl⟩
  have h := congrArg (fun U : (projectiveCusp K).Opens ↦ s K a ∈ U) (smooth_preimage K m hm)
  exact (Iff.of_eq h).mpr ⟨a, rfl⟩

/-- The actual scheme endomorphism of the smooth cusp locus. -/
def smoothMap : (cuspPuncturedOpen K).toScheme ⟶ (cuspPuncturedOpen K).toScheme :=
  IsOpenImmersion.lift (s K) (s K ≫ f K m hm) (smooth_image K m hm)

theorem smooth_isPullback : IsPullback (smoothMap K m hm) (s K) (s K) (f K m hm) :=
  IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm
    (smooth_preimage K m hm)

end
end ManuscriptAudit.CuspRelativePowerSmoothOpen

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.CuspRelativePowerSmoothOpen.smooth_isPullback
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
