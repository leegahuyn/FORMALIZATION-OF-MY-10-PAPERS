import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8FiniteCellReconstruction
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassGridError

/-! Finite-dimensional approximation of the actual smooth odd Maass core in its quotient L² norm. -/

namespace ManuscriptAudit.Paper8OddMaassGridApproximation

open Filter MeasureTheory Set UpperHalfPlane
open Paper8OddMaassHilbertCore Paper8OddMaassEnergyCompletion Paper8OddMaassGraphNorm
open Paper8OddMaassLevelFourTail Paper8OddMaassCuspTailEstimate Paper8OddGlobalCutoffEnergy
open Paper8OddMaassGridCells Paper8OddMaassGridError Paper8FiniteCellReconstruction
open Paper8ModularCoreRectangle Paper8OddCosetChartTransition FiniteIndexWeightZeroCosets
open scoped ENNReal

noncomputable section

def oddTailApproximationCoefficient (T : ℝ) : ℝ≥0∞ :=
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  ENNReal.ofReal (oddCuspTailConstant / T ^ 2) * (Fintype.card levelFourRightCoset : ℝ≥0∞)

def oddGridApproximationCoefficient (T δ : ℝ) : ℝ≥0∞ :=
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  ENNReal.ofReal ((coreMinimumHeight ^ 2)⁻¹) * ENNReal.ofReal (2 * δ ^ 2) *
    (ENNReal.ofReal (3 / coreMinimumHeight ^ 2) * ENNReal.ofReal (T ^ 2) * 2 *
      (Fintype.card levelFourRightCoset : ℝ≥0∞))

theorem exists_oddMaass_gridApprox {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {T δ : ℝ} (hT : 2 < T) (X Y : ℕ → ℝ) (hX : StrictMono X) (hY : StrictMono Y)
    (hX₀ : X 0 = -(1 / 2)) (hXn : X n = 1 / 2)
    (hY₀ : Y 0 = coreMinimumHeight) (hYm : Y m = T)
    (hXδ : ∀ i < n, X (i + 1) - X i ≤ δ) (hYδ : ∀ j < m, Y (j + 1) - Y j ≤ δ) :
    ∃ K : Submodule ℂ OddMaassL2, FiniteDimensional ℂ K ∧
      ∀ f : OddSmoothCompactCore, ∃ v ∈ K,
        ENNReal.ofReal (‖oddCoreVector f - v‖ ^ 2) ≤
          (oddTailApproximationCoefficient T + oddGridApproximationCoefficient T δ) *
            ENNReal.ofReal (‖oddCoreEnergyGraph f‖ ^ 2) := by
  classical
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  letI : IsFiniteMeasure oddMaassMeasure := oddMaassMeasure_finite
  let I := Fin (Fintype.card (OddGridTile n m))
  let e : OddGridTile n m ≃ I := Fintype.equivFin _
  let C (i : I) := oddGridCell X Y (e.symm i)
  let u (i : I) := oddGridPhase (e.symm i)
  have hC (i : I) : MeasurableSet (C i) := measurable_oddGridCell X Y (e.symm i)
  have hu (i : I) : Continuous (u i) := continuous_oddGridPhase (e.symm i)
  have hN (i : I) (z : ℍ) : ‖u i z‖ ≤ 1 := (norm_oddGridPhase (e.symm i) z).le
  obtain ⟨K, hK, hApprox⟩ :=
    exists_finiteDimensional_phaseCellReconstruction (μ := oddMaassMeasure) C hC u
      (fun i => (hu i).measurable) hN
  refine ⟨K, hK, ?_⟩
  intro f
  let a (i : I) := oddGridCoefficient X Y f (e.symm i)
  obtain ⟨v, hvK, hv⟩ := hApprox a
  refine ⟨v, hvK, ?_⟩
  let F : ℍ → ℂ := fun z => (f : ℂ → ℂ) z
  let U := ⋃ i, C i
  let M (z : ℍ) := ENNReal.ofReal (‖F z‖ ^ 2)
  let B (i : I) (z : ℍ) := ENNReal.ofReal (‖F z - a i * u i z‖ ^ 2)
  have hU : MeasurableSet U := MeasurableSet.iUnion hC
  have hM : Measurable M := ENNReal.measurable_ofReal.comp ((oddCore_continuous f).norm.pow 2).measurable
  have hB (i : I) : Measurable (B i) := ENNReal.measurable_ofReal.comp
    (((oddCore_continuous f).sub (continuous_const.mul (hu i))).norm.pow 2).measurable
  have hCover : levelFourCells \ levelFourCuspTail T ⊆ U := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (levelFour_core_subset_iUnion_grid hn hm X Y hX₀ hXn hY₀ hYm hz)
    refine mem_iUnion.mpr ⟨e i, ?_⟩
    simpa only [C, Equiv.symm_apply_apply] using hi
  have hSub : Uᶜ ∩ levelFourCells ⊆ levelFourCuspTail T := by
    intro z hz
    by_contra hZ
    exact hz.1 (hCover ⟨hz.2, hZ⟩)
  have hDiff : (↑(oddCoreVector f - v) : ℍ → ℂ) =ᵐ[oddMaassMeasure]
      fun z => F z - phaseCellReconstruction C u a z := by
    filter_upwards [Lp.coeFn_sub (oddCoreVector f) v, MemLp.coeFn_toLp (oddCore_memLp f), hv] with z h₁ h₂ h₃
    change (oddCoreVector f - v) z = oddCoreVector f z - v z at h₁
    change oddCoreVector f z = F z at h₂
    change v z = phaseCellReconstruction C u a z at h₃
    rw [h₁, h₂, h₃]
  have hNorm :
      ENNReal.ofReal (‖oddCoreVector f - v‖ ^ 2) =
        ∫⁻ z, ENNReal.ofReal (‖F z - phaseCellReconstruction C u a z‖ ^ 2) ∂oddMaassMeasure := by
    rw [← lintegral_coe_Lp_sq_norm_eq]
    apply lintegral_congr_ae
    filter_upwards [hDiff] with z hz
    rw [hz]
  have hBI (i : I) : (∫⁻ z, (C i).indicator (B i) z ∂oddMaassMeasure) =
      ∫⁻ z in C i, B i z ∂oddMaassMeasure :=
    lintegral_indicator (hC i) (B i)
  have hTail : (∫⁻ z in Uᶜ, M z ∂oddMaassMeasure) ≤
      oddTailApproximationCoefficient T * ENNReal.ofReal (‖oddCoreEnergyGraph f‖ ^ 2) := by
    rw [oddMaassMeasure, Measure.restrict_restrict hU.compl]
    exact (lintegral_mono_set hSub).trans (lintegral_levelFourCuspTail_le_graphNorm f hT)
  have hGrid : (∑ i : I, ∫⁻ z in C i, B i z ∂oddMaassMeasure) ≤
      oddGridApproximationCoefficient T δ * ENNReal.ofReal (‖oddCoreEnergyGraph f‖ ^ 2) := by
    calc
      _ ≤ ∑ i : I, ∫⁻ z in C i, B i z := by
        apply Finset.sum_le_sum
        intro i _
        apply lintegral_mono' (Measure.restrict_mono_measure Measure.restrict_le_self (C i))
        exact le_rfl
      _ = ∑ i : OddGridTile n m, ∫⁻ z in oddGridCell X Y i,
          ENNReal.ofReal (‖F z - oddGridCoefficient X Y f i * oddGridPhase i z‖ ^ 2) :=
        Fintype.sum_equiv e.symm _ _ (fun i => rfl)
      _ ≤ _ := sum_oddGridCell_lintegral_error_le f X Y hX hY hX₀ hXn hY₀ hYm hXδ hYδ
  calc
    _ = ∫⁻ z, ENNReal.ofReal (‖F z - phaseCellReconstruction C u a z‖ ^ 2) ∂oddMaassMeasure := hNorm
    _ ≤ ∫⁻ z, Uᶜ.indicator M z + ∑ i, (C i).indicator (B i) z ∂oddMaassMeasure :=
      lintegral_mono (phaseCellReconstruction_error_le C u a F)
    _ = (∫⁻ z in Uᶜ, M z ∂oddMaassMeasure) + ∑ i : I, ∫⁻ z in C i, B i z ∂oddMaassMeasure := by
      rw [lintegral_add_left (hM.indicator hU.compl), lintegral_indicator hU.compl,
        lintegral_finsetSum _ (fun i _ => (hB i).indicator (hC i))]
      simp only [hBI]
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add hTail hGrid

end
end ManuscriptAudit.Paper8OddMaassGridApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassGridApproximation.exists_oddMaass_gridApprox
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
