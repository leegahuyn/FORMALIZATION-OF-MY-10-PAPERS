import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Finset.Max

/-! Reconstruct a finite-dimensional L² approximant from measurable cells and fixed phases. -/

namespace ManuscriptAudit.Paper8FiniteCellReconstruction

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α ι : Type*} [Fintype ι] [LinearOrder ι]

def selectedCell (C : ι → Set α) (i : ι) : Set α :=
  C i \ ⋃ j : {j : ι // j < i}, C j.1

theorem selectedCell_subset (C : ι → Set α) (i : ι) : selectedCell C i ⊆ C i :=
  diff_subset

theorem measurable_selectedCell [MeasurableSpace α] {C : ι → Set α}
    (hC : ∀ i, MeasurableSet (C i)) (i : ι) : MeasurableSet (selectedCell C i) :=
  (hC i).diff (MeasurableSet.iUnion fun j => hC j.1)

theorem selectedCell_disjoint (C : ι → Set α) :
    Pairwise (fun i j => Disjoint (selectedCell C i) (selectedCell C j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact hj.2 (mem_iUnion.mpr ⟨⟨i, h⟩, hi.1⟩)
  · exact hi.2 (mem_iUnion.mpr ⟨⟨j, h⟩, hj.1⟩)

theorem iUnion_selectedCell (C : ι → Set α) : (⋃ i, selectedCell C i) = ⋃ i, C i := by
  classical
  ext z
  constructor
  · rintro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i, hi.1⟩
  · rintro hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    let s : Finset ι := Finset.univ.filter fun j => z ∈ C j
    have hiS : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hs : s.Nonempty := ⟨i, hiS⟩
    let j := s.min' hs
    have hjS : j ∈ s := Finset.min'_mem s hs
    refine mem_iUnion.mpr ⟨j, (Finset.mem_filter.mp hjS).2, ?_⟩
    intro h
    obtain ⟨k, hk⟩ := mem_iUnion.mp h
    have hkS : k.1 ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    exact (not_le_of_gt k.2) (s.min'_le k.1 hkS)

def phaseCellReconstruction (C : ι → Set α) (u : ι → α → ℂ) (a : ι → ℂ) (z : α) : ℂ :=
  ∑ i, a i * (selectedCell C i).indicator (u i) z

theorem phaseCellReconstruction_of_mem {C : ι → Set α} (u : ι → α → ℂ) (a : ι → ℂ)
    {i : ι} {z : α} (hz : z ∈ selectedCell C i) :
    phaseCellReconstruction C u a z = a i * u i z := by
  classical
  unfold phaseCellReconstruction
  rw [Finset.sum_eq_single i]
  · rw [indicator_of_mem hz]
  · intro j _ hji
    have hOut : z ∉ selectedCell C j :=
      fun hj => Set.disjoint_left.mp (selectedCell_disjoint C hji.symm) hz hj
    rw [indicator_of_notMem hOut, mul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem phaseCellReconstruction_of_notMem {C : ι → Set α} (u : ι → α → ℂ) (a : ι → ℂ)
    {z : α} (hz : z ∉ ⋃ i, C i) : phaseCellReconstruction C u a z = 0 := by
  classical
  unfold phaseCellReconstruction
  apply Finset.sum_eq_zero
  intro i _
  rw [indicator_of_notMem (fun h => hz (mem_iUnion.mpr ⟨i, h.1⟩)), mul_zero]

theorem phaseCellReconstruction_error_le (C : ι → Set α) (u : ι → α → ℂ) (a : ι → ℂ)
    (F : α → ℂ) (z : α) :
    ENNReal.ofReal (‖F z - phaseCellReconstruction C u a z‖ ^ 2) ≤
      (⋃ i, C i)ᶜ.indicator (fun w => ENNReal.ofReal (‖F w‖ ^ 2)) z +
        ∑ i, (C i).indicator (fun w => ENNReal.ofReal (‖F w - a i * u i w‖ ^ 2)) z := by
  classical
  by_cases h : z ∈ ⋃ i, C i
  · have hz : z ∈ ⋃ i, selectedCell C i := by rwa [iUnion_selectedCell]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hCompl : z ∉ (⋃ i, C i)ᶜ := fun hz => hz h
    rw [phaseCellReconstruction_of_mem u a hi, indicator_of_notMem hCompl, zero_add]
    conv_lhs => rw [← indicator_of_mem (show z ∈ C i from hi.1)]
    exact Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)
  · have hCompl : z ∈ (⋃ i, C i)ᶜ := h
    rw [phaseCellReconstruction_of_notMem u a h, sub_zero, indicator_of_mem hCompl]
    exact le_add_of_nonneg_right (zero_le _)

variable [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

private theorem selectedCell_phase_memLp {C : ι → Set α} (hC : ∀ i, MeasurableSet (C i))
    {u : ι → α → ℂ} (hu : ∀ i, Measurable (u i)) (hu₁ : ∀ i z, ‖u i z‖ ≤ 1) (i : ι) :
    MemLp ((selectedCell C i).indicator (u i)) 2 μ := by
  have hMeas := (hu i).indicator (measurable_selectedCell hC i)
  apply MemLp.of_bound hMeas.aestronglyMeasurable 1
  apply Eventually.of_forall
  intro z
  by_cases hz : z ∈ selectedCell C i
  · rw [indicator_of_mem hz]
    exact hu₁ i z
  · simp [indicator_of_notMem hz]

theorem exists_finiteDimensional_phaseCellReconstruction (C : ι → Set α)
    (hC : ∀ i, MeasurableSet (C i)) (u : ι → α → ℂ)
    (hu : ∀ i, Measurable (u i)) (hu₁ : ∀ i z, ‖u i z‖ ≤ 1) :
    ∃ K : Submodule ℂ (Lp ℂ 2 μ), FiniteDimensional ℂ K ∧
      ∀ a : ι → ℂ, ∃ v ∈ K, ⇑v =ᵐ[μ] phaseCellReconstruction C u a := by
  classical
  let b (i : ι) : Lp ℂ 2 μ := (selectedCell_phase_memLp hC hu hu₁ i).toLp
    ((selectedCell C i).indicator (u i))
  let K := Submodule.span ℂ (range b)
  refine ⟨K, FiniteDimensional.span_of_finite ℂ (finite_range b), ?_⟩
  intro a
  let v := ∑ i, a i • b i
  have hK : v ∈ K := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem K _ (Submodule.subset_span (mem_range_self i))
  refine ⟨v, hK, ?_⟩
  have hAll : ∀ᵐ z ∂μ, ∀ i : ι, (a i • b i) z = a i * (selectedCell C i).indicator (u i) z := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (a i) (b i), MemLp.coeFn_toLp
      (selectedCell_phase_memLp (μ := μ) hC hu hu₁ i)] with z h₁ h₂
    change _ = _ at h₁
    change b i z = _ at h₂
    simp only [h₁, Pi.smul_apply, h₂, smul_eq_mul]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • b i), hAll] with z hSum hz
  change v z = _
  rw [hSum]
  simp only [phaseCellReconstruction, hz]

end
end ManuscriptAudit.Paper8FiniteCellReconstruction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8FiniteCellReconstruction.phaseCellReconstruction_error_le,
      ``ManuscriptAudit.Paper8FiniteCellReconstruction.exists_finiteDimensional_phaseCellReconstruction] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
