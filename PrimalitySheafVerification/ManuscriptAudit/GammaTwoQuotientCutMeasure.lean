import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ThetaChosenQuotientAnalysis

/-! The quotient measure is the actual restricted hyperbolic measure on a set with disjoint translates. -/

namespace ManuscriptAudit.GammaTwoQuotientCutMeasure

open Function MeasureTheory Set
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane Pointwise

noncomputable section

private theorem preimage_quotient_image (A : Set ℍ) :
    gammaTwoQuotientMk ⁻¹' (gammaTwoQuotientMk '' A) = ⋃ g : GammaTwoEffective, g • A := by
  ext z
  constructor
  · rintro ⟨w, hw, hq⟩
    obtain ⟨g, hg⟩ : MulAction.orbitRel GammaTwoEffective ℍ w z := Quotient.exact hq
    refine mem_iUnion.2 ⟨g⁻¹, ?_⟩
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv, hg]
    exact hw
  · rintro hz
    obtain ⟨g, hg⟩ := mem_iUnion.1 hz
    have hA : g⁻¹ • z ∈ A := (mem_smul_set_iff_inv_smul_mem).mp hg
    exact ⟨g⁻¹ • z, hA, gammaTwoQuotientMk_smul _ _⟩

theorem quotient_image_measure_eq (D : GammaTwoFundamentalDomain)
    {A : Set ℍ} (hA : MeasurableSet A)
    (hCut : Pairwise (Disjoint on fun g : GammaTwoEffective => g • A)) :
    D.quotientMeasure (gammaTwoQuotientMk '' A) = hyperbolicMeasure A := by
  have hm : Measurable gammaTwoQuotientMk := measurable_quotient_mk''
  have hImage := GammaTwoFundamentalDomain.quotientImage_measurable hA
  have hUnion : (⋃ g : GammaTwoEffective, g • A) ∩ D.carrier =
      ⋃ g : GammaTwoEffective, (g • A ∩ D.carrier) := by
    ext z
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨⟨g, hg⟩, hd⟩
      exact ⟨g, hg, hd⟩
    · rintro ⟨g, hg, hd⟩
      exact ⟨⟨g, hg⟩, hd⟩
  have hM (g : GammaTwoEffective) : MeasurableSet (g • A ∩ D.carrier) :=
    (MeasurableSet.const_smul hA g).inter D.carrier_measurable
  have hDisj : Pairwise (Disjoint on fun g : GammaTwoEffective => g • A ∩ D.carrier) := by
    intro g h hgh
    exact (hCut hgh).mono inter_subset_left inter_subset_left
  rw [GammaTwoFundamentalDomain.quotientMeasure, Measure.map_apply hm hImage,
    Measure.restrict_apply (hm hImage), preimage_quotient_image, hUnion, measure_iUnion hDisj hM]
  exact (D.isFundamental.measure_eq_tsum A).symm

theorem map_restrict_eq (D : GammaTwoFundamentalDomain)
    {A : Set ℍ} (hA : MeasurableSet A)
    (hCut : Pairwise (Disjoint on fun g : GammaTwoEffective => g • A)) :
    (hyperbolicMeasure.restrict A).map gammaTwoQuotientMk =
      D.quotientMeasure.restrict (gammaTwoQuotientMk '' A) := by
  have hm : Measurable gammaTwoQuotientMk := measurable_quotient_mk''
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hm hB, Measure.restrict_apply (hm hB), Measure.restrict_apply hB]
  have hImage :
      gammaTwoQuotientMk '' (gammaTwoQuotientMk ⁻¹' B ∩ A) = B ∩ gammaTwoQuotientMk '' A := by
    ext q
    constructor
    · rintro ⟨z, ⟨hzB, hzA⟩, rfl⟩
      exact ⟨hzB, ⟨z, hzA, rfl⟩⟩
    · rintro ⟨hqB, z, hz, rfl⟩
      exact ⟨z, ⟨hqB, hz⟩, rfl⟩
  rw [← hImage]
  symm
  apply quotient_image_measure_eq D ((hm hB).inter hA)
  intro g h hgh
  apply (hCut hgh).mono
  · simpa only [image_smul] using
      (image_mono inter_subset_right :
        (g • ·) '' (gammaTwoQuotientMk ⁻¹' B ∩ A) ⊆ (g • ·) '' A)
  · simpa only [image_smul] using
      (image_mono inter_subset_right :
        (h • ·) '' (gammaTwoQuotientMk ⁻¹' B ∩ A) ⊆ (h • ·) '' A)

end
end ManuscriptAudit.GammaTwoQuotientCutMeasure

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GammaTwoQuotientCutMeasure.quotient_image_measure_eq,
      ``ManuscriptAudit.GammaTwoQuotientCutMeasure.map_restrict_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
