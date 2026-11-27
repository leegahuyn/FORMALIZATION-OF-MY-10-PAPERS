import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCosetMass

/-! The modular-domain boundary is null for the actual hyperbolic volume. -/

namespace ManuscriptAudit.Paper8EtaCosetBoundary

open Set Metric MeasureTheory UpperHalfPlane
open Paper8EtaPeterssonMass Paper8EtaCosetMass
open FiniteIndexWeightZeroCosets (RightCoset)
open scoped MatrixGroups ENNReal

private theorem volume_vertical_eq_zero (a : ℝ) :
    (volume : Measure ℂ) {z : ℂ | z.re = a} = 0 := by
  let S : Set (ℝ × ℝ) := {a} ×ˢ (univ : Set ℝ)
  have hS : MeasurableSet S := (measurableSet_singleton a).prod MeasurableSet.univ
  have hPre : Complex.measurableEquivRealProd ⁻¹' S = {z : ℂ | z.re = a} := by
    ext z
    simp [S]
  rw [← hPre, Complex.volume_preserving_equiv_real_prod.measure_preimage hS.nullMeasurableSet]
  change (volume : Measure ℝ).prod volume ({a} ×ˢ (univ : Set ℝ)) = 0
  rw [Measure.prod_prod, measure_singleton, zero_mul]

theorem volume_fd_boundary_zero :
    (volume : Measure ℍ) (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply setLIntegral_measure_zero
  let B : Set ℂ := sphere 0 1 ∪ ({z : ℂ | z.re = (1 : ℝ) / 2} ∪ {z : ℂ | z.re = -(1 : ℝ) / 2})
  have hB : (volume : Measure ℂ) B = 0 := by
    exact measure_union_null (Measure.addHaar_sphere volume 0 1)
      (measure_union_null (volume_vertical_eq_zero ((1 : ℝ) / 2))
        (volume_vertical_eq_zero (-(1 : ℝ) / 2)))
  refine measure_mono_null (s := ((↑) : ℍ → ℂ) '' (ModularGroup.fd \ ModularGroup.fdo)) ?_ hB
  rintro _ ⟨z, hz, rfl⟩
  have hzNorm : 1 ≤ ‖(z : ℂ)‖ := Complex.one_le_normSq_iff.mp hz.1.1
  by_cases! hzStrict : 1 < ‖(z : ℂ)‖
  · have hzAbs : |z.re| = 1 / 2 := le_antisymm hz.1.2 (le_of_not_gt (fun h =>
      hz.2 ⟨Complex.one_lt_normSq_iff.mpr hzStrict, h⟩))
    change (z : ℂ) ∈ B
    rcases abs_cases z.re with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact Or.inr (Or.inl (by change z.re = 1 / 2; linarith [ha]))
    · exact Or.inr (Or.inr (by change z.re = -1 / 2; linarith [ha]))
  · have hNorm : ‖(z : ℂ)‖ = 1 := le_antisymm hzStrict hzNorm
    exact Or.inl (by simpa only [Metric.mem_sphere, dist_zero_right] using hNorm)

theorem volume_translate_eq (g : SL(2, ℤ)) (S : Set ℍ) :
    (volume : Measure ℍ) (translate g S) = (volume : Measure ℍ) S := by
  have hMeasure : MeasurePreserving (fun z : ℍ => g • z) (volume : Measure ℍ) volume :=
    measurePreserving_smul (g : GL (Fin 2) ℝ) volume
  have hEmb : MeasurableEmbedding (fun z : ℍ => g • z) :=
    measurableEmbedding_const_smul (g : GL (Fin 2) ℝ)
  simpa only [translate, lintegral_const, Measure.restrict_apply_univ, one_mul] using
    (hMeasure.setLIntegral_comp_emb hEmb (fun _ : ℍ => (1 : ℝ≥0∞)) S).symm

theorem coset_cells_boundary_volume_zero (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    (volume : Measure ℍ) (cosetCells H ModularGroup.fd \ cosetCells H ModularGroup.fdo) = 0 := by
  letI := FiniteIndexWeightZeroCosets.rightCosetFintype H
  let B := ⋃ q : RightCoset H, translate (cellRepresentative H q) (ModularGroup.fd \ ModularGroup.fdo)
  have hB : (volume : Measure ℍ) B = 0 := by
    have hUnion := measure_iUnion_le (μ := (volume : Measure ℍ))
      (fun q : RightCoset H => translate (cellRepresentative H q) (ModularGroup.fd \ ModularGroup.fdo))
    simpa only [B, volume_translate_eq, volume_fd_boundary_zero, tsum_zero, nonpos_iff_eq_zero] using hUnion
  refine measure_mono_null (fun z hz => ?_) hB
  obtain ⟨q, u, hu, rfl⟩ := mem_iUnion.mp hz.1
  have huNot : u ∉ ModularGroup.fdo := fun h =>
    hz.2 (mem_iUnion.mpr ⟨q, u, h, rfl⟩)
  exact mem_iUnion.mpr ⟨q, u, ⟨hu, huNot⟩, rfl⟩

theorem closed_cells_ae_eq_open (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    cosetCells H ModularGroup.fd =ᵐ[(volume : Measure ℍ)] cosetCells H ModularGroup.fdo := by
  refine ae_eq_set.mpr ⟨coset_cells_boundary_volume_zero H, ?_⟩
  have hSub : cosetCells H ModularGroup.fdo ⊆ cosetCells H ModularGroup.fd := by
    intro z hz
    obtain ⟨q, w, hw, rfl⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨q, w, ModularGroup.fdo_subset_fd hw, rfl⟩
  simp [sdiff_eq_empty.mpr hSub]

theorem open_cells_meet_ae_orbit (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    ∀ᵐ z : ℍ ∂(volume : Measure ℍ),
      ∃ h : H, ∃ w ∈ cosetCells H ModularGroup.fdo, (h : SL(2, ℤ)) • w = z := by
  letI : Countable SL(2, ℤ) := Countable.of_injective
    (fun g : SL(2, ℤ) => (g.1 : Matrix (Fin 2) (Fin 2) ℤ)) Subtype.val_injective
  letI : Countable H := Countable.of_injective (fun h : H => (h : SL(2, ℤ))) Subtype.val_injective
  let B := ⋃ h : H, translate (h : SL(2, ℤ))
    (cosetCells H ModularGroup.fd \ cosetCells H ModularGroup.fdo)
  have hNull : (volume : Measure ℍ) B = 0 := by
    have hUnion := measure_iUnion_le (μ := (volume : Measure ℍ))
      (fun h : H => translate (h : SL(2, ℤ)) (cosetCells H ModularGroup.fd \ cosetCells H ModularGroup.fdo))
    simpa only [B, volume_translate_eq, coset_cells_boundary_volume_zero H, tsum_zero,
      nonpos_iff_eq_zero] using hUnion
  have hAE : ∀ᵐ z : ℍ ∂(volume : Measure ℍ), z ∉ B := by
    simpa only [ae_iff, not_not, setOf_mem_eq] using hNull
  filter_upwards [hAE] with z hz
  obtain ⟨h, w, hw, he⟩ := closed_cells_meet_every_orbit H z
  refine ⟨h, w, ?_, he⟩
  by_contra hNo
  exact hz (mem_iUnion.mpr ⟨h, w, ⟨hw, hNo⟩, he⟩)

end ManuscriptAudit.Paper8EtaCosetBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaCosetBoundary.volume_fd_boundary_zero,
      ``ManuscriptAudit.Paper8EtaCosetBoundary.volume_translate_eq,
      ``ManuscriptAudit.Paper8EtaCosetBoundary.coset_cells_boundary_volume_zero,
      ``ManuscriptAudit.Paper8EtaCosetBoundary.closed_cells_ae_eq_open,
      ``ManuscriptAudit.Paper8EtaCosetBoundary.open_cells_meet_ae_orbit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
