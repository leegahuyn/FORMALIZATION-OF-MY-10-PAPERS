import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspRelativePowerOpenRanges

/-! The cusp power endomorphism pulls back both opens of the genuine
two-chart cover and their actual Laurent intersection to themselves. -/

namespace ManuscriptAudit.CuspRelativePowerCartesian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspProperYChart (lineOpen affine_chart_cover)
open CuspChartIntersection (overlapIsoLaurent)
open CuspChartIntersectionMaps (overlapIsoLaurent_inv_toAffineCusp
  overlapIsoLaurent_inv_toAffineLine)
open CuspRelativePowerMap
open CuspRelativePowerOpenRanges (power_line_preimage power_affine_preimage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] (m : ℕ) (hm : 2 ≤ m)

private abbrev P := projectiveCusp K
private abbrev L := Spec (CommRingCat.of (Polynomial K))
private abbrev A := affineCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev f := projectiveMap K m hm
private abbrev W := pullback (j K) (k K)

private theorem mem_cover (x : P K) : x ∈ Set.range (j K) ∪ Set.range (k K) := by
  have h : Set.range (j K) ∪ Set.range (k K) = Set.univ :=
    congrArg (fun U : (P K).Opens ↦ (U : Set (P K))) (affine_chart_cover K)
  rw [h]
  exact Set.mem_univ x

private theorem map_apply_affine (a : A K) :
    f K m hm (j K a) = j K (affineMap K m hm a) :=
  congrArg (fun g : A K ⟶ P K ↦ g a) (affine_projectiveMap K m hm)

private theorem map_apply_line (b : L K) :
    f K m hm (k K b) = k K (lineMap K m b) :=
  congrArg (fun g : L K ⟶ P K ↦ g b) (line_projectiveMap K m hm)

/-- The native affine cusp open is invariant under the relative power. -/
theorem affine_preimage : f K m hm ⁻¹ᵁ (j K).opensRange = (j K).opensRange := by
  ext x
  change f K m hm x ∈ Set.range (j K) ↔ x ∈ Set.range (j K)
  rcases mem_cover K x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [map_apply_affine]
    exact iff_of_true ⟨_, rfl⟩ ⟨_, rfl⟩
  · rw [map_apply_line]
    exact Iff.of_eq (congrArg (fun U : (L K).Opens ↦ b ∈ U)
      (power_line_preimage K m (lt_of_lt_of_le (by decide : 0 < 2) hm)))

/-- The native infinity chart is also invariant. -/
theorem line_preimage : f K m hm ⁻¹ᵁ (k K).opensRange = (k K).opensRange := by
  ext x
  change f K m hm x ∈ Set.range (k K) ↔ x ∈ Set.range (k K)
  rcases mem_cover K x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [map_apply_affine]
    exact Iff.of_eq (congrArg (fun U : (A K).Opens ↦ a ∈ U) (power_affine_preimage K m hm))
  · rw [map_apply_line]
    exact iff_of_true ⟨_, rfl⟩ ⟨_, rfl⟩

theorem affine_isPullback : IsPullback (affineMap K m hm) (j K) (j K) (f K m hm) :=
  IsOpenImmersion.isPullback _ _ _ _ (affine_projectiveMap K m hm) (affine_preimage K m hm)

theorem line_isPullback : IsPullback (lineMap K m) (k K) (k K) (f K m hm) :=
  IsOpenImmersion.isPullback _ _ _ _ (line_projectiveMap K m hm) (line_preimage K m hm)

/-- The relative Laurent map transported to the literal overlap. -/
def overlapEndomorphism : W K ⟶ W K :=
  (overlapIsoLaurent K).hom ≫ overlapMap K m ≫ (overlapIsoLaurent K).inv

@[reassoc]
theorem overlapEndomorphism_fst :
    overlapEndomorphism K m ≫ pullback.fst (j K) (k K) =
      pullback.fst (j K) (k K) ≫ affineMap K m hm := by
  unfold overlapEndomorphism
  rw [Category.assoc, Category.assoc, overlapIsoLaurent_inv_toAffineCusp,
    ← affine_overlap_commutes, ← Category.assoc]
  have h : (overlapIsoLaurent K).hom ≫ CuspChartIntersectionMaps.laurentToAffineCusp K =
      pullback.fst (j K) (k K) := by
    rw [← overlapIsoLaurent_inv_toAffineCusp, Iso.hom_inv_id_assoc]
  rw [h]

@[reassoc]
theorem overlapEndomorphism_snd :
    overlapEndomorphism K m ≫ pullback.snd (j K) (k K) =
      pullback.snd (j K) (k K) ≫ lineMap K m := by
  unfold overlapEndomorphism
  rw [Category.assoc, Category.assoc, overlapIsoLaurent_inv_toAffineLine,
    ← line_overlap_commutes, ← Category.assoc, CuspChartIntersection.overlapIsoLaurent_hom_toAffineLine]

/-- The overlap inclusion is the actual common open immersion, via the first chart. -/
abbrev overlapInclusion : W K ⟶ P K :=
  pullback.fst (j K) (k K) ≫ j K

theorem overlap_preimage :
    f K m hm ⁻¹ᵁ (overlapInclusion K).opensRange = (overlapInclusion K).opensRange := by
  have h : (overlapInclusion K).opensRange = (j K).opensRange ⊓ (k K).opensRange := by
    rw [overlapInclusion, Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_pullbackFst,
      Scheme.Hom.image_preimage_eq_opensRange_inf]
  rw [h]
  ext x
  have hA := congrArg (fun U : (P K).Opens ↦ x ∈ U) (affine_preimage K m hm)
  have hB := congrArg (fun U : (P K).Opens ↦ x ∈ U) (line_preimage K m hm)
  exact (and_congr (Iff.of_eq hA) (Iff.of_eq hB))

/-- The actual Laurent overlap square is cartesian as well. -/
theorem overlap_isPullback :
    IsPullback (overlapEndomorphism K m) (overlapInclusion K) (overlapInclusion K) (f K m hm) := by
  apply IsOpenImmersion.isPullback
  · rw [overlapInclusion, Category.assoc, affine_projectiveMap, ← Category.assoc,
      ← overlapEndomorphism_fst K m hm, Category.assoc]
  · exact overlap_preimage K m hm

end
end ManuscriptAudit.CuspRelativePowerCartesian

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspRelativePowerCartesian.affine_isPullback,
      ``ManuscriptAudit.CuspRelativePowerCartesian.line_isPullback,
      ``ManuscriptAudit.CuspRelativePowerCartesian.overlap_isPullback] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
