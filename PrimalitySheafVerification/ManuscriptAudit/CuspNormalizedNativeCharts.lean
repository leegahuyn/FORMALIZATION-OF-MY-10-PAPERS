import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProjectiveNormalizationAffine

/-! Both displayed affine lines are Cartesian charts of the actual
proper cusp normalization. -/

namespace ManuscriptAudit.CuspNormalizedNativeCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspProjectiveNormalization (normalizedCusp normalizationMap normalizationLineIso)
open CuspProjectiveNormalizationAffine (normalizationAffineIso normalizationAffineIso_inv_over)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

private abbrev L := Spec (CommRingCat.of (Polynomial K))
private abbrev m := normalizationMap K

abbrev affineInclusion : L K ⟶ normalizedCusp K :=
  (normalizationAffineIso K).inv ≫ pullback.fst (m K) (affineOpen K)

abbrev lineInclusion : L K ⟶ normalizedCusp K :=
  (normalizationLineIso K).inv ≫ pullback.fst (m K) (lineOpen K)

instance affineInclusion_open : IsOpenImmersion (affineInclusion K) := inferInstance
instance lineInclusion_open : IsOpenImmersion (lineInclusion K) := inferInstance

/-- Over the singular affine chart, the original affine normalization is Cartesian. -/
theorem affine_isPullback :
    IsPullback (affineInclusion K) (CuspScheme.cuspMap K) (m K) (affineOpen K) := by
  let e := normalizationAffineIso K
  refine (IsPullback.of_hasPullback (m K) (affineOpen K)).of_iso' e.symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id, affineInclusion]
  · simpa only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
      (normalizationAffineIso_inv_over K)
  · simp
  · simp

private theorem normalizationLineIso_hom :
    (normalizationLineIso K).hom = pullback.snd (m K) (lineOpen K) := rfl

/-- Over the regular affine chart, the original identity morphism is Cartesian. -/
theorem line_isPullback :
    IsPullback (lineInclusion K) (𝟙 (L K)) (m K) (lineOpen K) := by
  let e := normalizationLineIso K
  refine (IsPullback.of_hasPullback (m K) (lineOpen K)).of_iso' e.symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id, lineInclusion]
  · simp only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id, ← normalizationLineIso_hom,
      Iso.inv_hom_id]
  · simp
  · simp

theorem line_over : lineInclusion K ≫ m K = lineOpen K := by
  simpa only [Category.id_comp] using (line_isPullback K).w

end
end ManuscriptAudit.CuspNormalizedNativeCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNormalizedNativeCharts.affine_isPullback,
      ``ManuscriptAudit.CuspNormalizedNativeCharts.line_isPullback] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
