import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationZPolynomial
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartPrincipalOpen

/-! The actual normalization of the projective node is covered by its
polynomial Z chart and its original Y chart. Their overlap is the
displayed principal localization of the Y chart. -/

namespace ManuscriptAudit.NodalNormalizedNativeCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode affineOpen affineNode)
open NodalProjectiveNormalization (normalizedNode normalizationMap normalizationYChartIso)
open NodalNormalizationZPolynomial (normalizationZPolynomialIso)
open NodalProperYChart (chartOpen)
open NodalYChartImmersion (nodeYChart)
open NodalYChartOverlap (overlapRing)
open NodalYChartPrincipalOpen (principalInclusion overlapEtaleIso overlapEtaleIso_snd overlapObject)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev m := normalizationMap K
private abbrev y := chartOpen K
private abbrev z := affineOpen K

abbrev yToNormalized : nodeYChart K ⟶ normalizedNode K :=
  (normalizationYChartIso K).inv ≫ pullback.fst (m K) (y K)

instance yToNormalized_open : IsOpenImmersion (yToNormalized K) := inferInstance

private theorem y_chart_iso_hom :
    (normalizationYChartIso K).hom = pullback.snd (m K) (y K) := rfl

theorem yToNormalized_over : yToNormalized K ≫ m K = y K := by
  change (normalizationYChartIso K).inv ≫ pullback.fst (m K) (y K) ≫ m K = y K
  rw [pullback.condition, ← y_chart_iso_hom, Iso.inv_hom_id_assoc]

theorem yToNormalized_isPullback :
    IsPullback (yToNormalized K) (𝟙 (nodeYChart K)) (m K) (y K) := by
  let e := normalizationYChartIso K
  refine (IsPullback.of_hasPullback (m K) (y K)).of_iso' e.symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id, yToNormalized]
  · simp only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id, ← y_chart_iso_hom,
      Iso.inv_hom_id]
  · simp
  · simp

variable (h2 : (2 : K) ≠ 0)

abbrev zToNormalized : Spec (CommRingCat.of (Polynomial K)) ⟶ normalizedNode K :=
  (normalizationZPolynomialIso K h2).inv ≫ pullback.fst (m K) (z K)

instance zToNormalized_open : IsOpenImmersion (zToNormalized K h2) := inferInstance

abbrev zToAffine : Spec (CommRingCat.of (Polynomial K)) ⟶ affineNode K :=
  (normalizationZPolynomialIso K h2).inv ≫ pullback.snd (m K) (z K)

theorem zToNormalized_isPullback :
    IsPullback (zToNormalized K h2) (zToAffine K h2) (m K) (z K) := by
  let e := normalizationZPolynomialIso K h2
  refine (IsPullback.of_hasPullback (m K) (z K)).of_iso' e.symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id, zToNormalized]
  · simp only [e, Iso.symm_hom, Iso.refl_hom, Category.comp_id, zToAffine]
  · simp
  · simp

private abbrev baseOverlap := pullback (z K) (y K)

private def baseOverlapIso : baseOverlap K ≅ Spec (CommRingCat.of (overlapRing K)) :=
  (Scheme.Etale.forget (projectiveNode K) ⋙ Over.forget (projectiveNode K)).mapIso
    (overlapEtaleIso K)

private theorem baseOverlapIso_snd :
    (baseOverlapIso K).hom ≫ principalInclusion K = pullback.snd (z K) (y K) := by
  exact congrArg (fun f : overlapObject K ⟶ Scheme.Etale.mk (chartOpen K) ↦ f.left)
    (overlapEtaleIso_snd K)

private theorem rightSquare :
    IsPullback (pullback.snd (m K) (z K)) (pullback.fst (m K) (z K)) (z K) (m K) :=
  (IsPullback.of_hasPullback (m K) (z K)).flip

private theorem outerSquare :
    IsPullback (pullback.fst (z K) (y K)) (pullback.snd (z K) (y K))
      (z K) (yToNormalized K ≫ m K) := by
  rw [yToNormalized_over]
  exact IsPullback.of_hasPullback (z K) (y K)

private def baseOverlapToNormalizedZ : baseOverlap K ⟶ pullback (m K) (z K) :=
  (rightSquare K).lift (pullback.fst (z K) (y K)) (pullback.snd (z K) (y K) ≫ yToNormalized K)
    (by rw [Category.assoc, yToNormalized_over, pullback.condition])

/-- The actual overlap arrow into the displayed polynomial normalization chart. -/
def overlapToZ : Spec (CommRingCat.of (overlapRing K)) ⟶ Spec (CommRingCat.of (Polynomial K)) :=
  (baseOverlapIso K).inv ≫ baseOverlapToNormalizedZ K ≫ (normalizationZPolynomialIso K h2).hom

/-- The displayed Y principal localization is the actual overlap of the normalized charts. -/
theorem overlap_isPullback :
    IsPullback (principalInclusion K) (overlapToZ K h2) (yToNormalized K) (zToNormalized K h2) := by
  have h : IsPullback (baseOverlapToNormalizedZ K) (pullback.snd (z K) (y K))
      (pullback.fst (m K) (z K)) (yToNormalized K) :=
    IsPullback.of_right' (outerSquare K) (rightSquare K)
  refine (h.of_iso (baseOverlapIso K) (normalizationZPolynomialIso K h2)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_).flip
  · simp only [overlapToZ, Iso.hom_inv_id_assoc]
  · simpa only [Iso.refl_hom, Category.comp_id] using (baseOverlapIso_snd K).symm
  · simp only [Iso.refl_hom, Category.comp_id, zToNormalized, Iso.hom_inv_id_assoc]
  · simp

end
end ManuscriptAudit.NodalNormalizedNativeCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedNativeCharts.yToNormalized_isPullback,
      ``ManuscriptAudit.NodalNormalizedNativeCharts.zToNormalized_isPullback,
      ``ManuscriptAudit.NodalNormalizedNativeCharts.overlap_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
