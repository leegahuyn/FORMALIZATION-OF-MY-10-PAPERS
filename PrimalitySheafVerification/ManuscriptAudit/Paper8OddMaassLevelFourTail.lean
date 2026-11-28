import Lean.Util.CollectAxioms
import Mathlib.Data.ENNReal.BigOperators
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassCuspTailEstimate
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassCovariantGradient

/-! Transport the uniform cusp estimate to the actual level-four union of cells. -/

namespace ManuscriptAudit.Paper8OddMaassLevelFourTail

open MeasureTheory Set UpperHalfPlane
open Paper8ModularHeightCutoff Paper8OddGlobalCutoffEnergy Paper8OddMaassHilbertCore
open Paper8OddMaassCovariantGradient Paper8MaassCovariantGeometry Paper8MaassCovariantPullback
open Paper8OddCosetChartTransition Paper8OddCosetChartEnergy Paper8OddMaassHorizontalPoincare
open Paper8OddMaassCuspTailEstimate Paper8EtaCosetMass FiniteIndexWeightZeroCosets
open Paper8EtaPeterssonMass (translate)
open scoped ENNReal MatrixGroups

noncomputable section

def levelFourCuspTail (T : ℝ) : Set ℍ := levelFourCells ∩ {z : ℍ | T ≤ maximumHeight z}

private theorem fd_height_iff_cusp_height {z : ℍ} (hz : z ∈ ModularGroup.fd) {T : ℝ} (hT : 2 < T) :
    T ≤ maximumHeight z ↔ T ≤ z.im := by
  constructor
  · intro h
    have hp : (1 / 2 : ℝ) ≤ z.im := by
      by_contra hn
      have hlt : z.im < 1 / 2 := lt_of_not_ge hn
      have hLow := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      have hSq := pow_lt_pow_left₀ hlt z.im_pos.le (by decide : 2 ≠ 0)
      norm_num at hSq
      linarith
    have hgt : 1 < z.im := by
      by_contra hn
      have hZ : z.im ≤ 1 := le_of_not_gt hn
      have hInv : 1 / z.im ≤ 2 := (div_le_iff₀ z.im_pos).2 (by linarith)
      have hmax : maximumHeight z ≤ 2 :=
        (maximumHeight_le_max z).trans (max_le (hZ.trans (by norm_num)) hInv)
      exact (not_le_of_gt hT) (h.trans hmax)
    simpa only [maximumHeight_eq_im_of_gt_one z hgt] using h
  · intro h
    exact h.trans (by simpa only [one_smul] using im_smul_le_maximumHeight z 1)

theorem levelFourCuspTail_eq_cosetCells {T : ℝ} (hT : 2 < T) :
    levelFourCuspTail T = cosetCells (CongruenceSubgroup.Gamma0 4) (standardCuspTail T) := by
  ext z
  constructor
  · rintro ⟨hz, hTz⟩
    obtain ⟨q, u, hu, rfl⟩ := mem_iUnion.mp hz
    change T ≤ maximumHeight (cellRepresentative (CongruenceSubgroup.Gamma0 4) q • u) at hTz
    rw [maximumHeight_invariant] at hTz
    exact mem_iUnion.mpr ⟨q, u, ⟨hu, (fd_height_iff_cusp_height hu hT).mp hTz⟩, rfl⟩
  · intro hz
    obtain ⟨q, u, hu, rfl⟩ := mem_iUnion.mp hz
    refine ⟨mem_iUnion.mpr ⟨q, u, hu.1, rfl⟩, ?_⟩
    change T ≤ maximumHeight (cellRepresentative (CongruenceSubgroup.Gamma0 4) q • u)
    rw [maximumHeight_invariant]
    exact (fd_height_iff_cusp_height hu.1 hT).mpr hu.2

def oddCoreGraphDensity (f : OddSmoothCompactCore) (z : ℍ) : ℝ :=
  maassCovariantEnergy (f : ℂ → ℂ) z + ‖(f : ℂ → ℂ) z‖ ^ 2

theorem oddCoreGraphDensity_nonneg (f : OddSmoothCompactCore) (z : ℍ) :
    0 ≤ oddCoreGraphDensity f z := by
  unfold oddCoreGraphDensity maassCovariantEnergy
  positivity

theorem oddCoreGraphDensity_eq (f : OddSmoothCompactCore) (z : ℍ) :
    oddCoreGraphDensity f z =
      ‖oddCovariantDirection 1 (Complex.I / 4) f z‖ ^ 2 +
      ‖oddCovariantDirection Complex.I 0 f z‖ ^ 2 + ‖(f : ℂ → ℂ) z‖ ^ 2 := by
  unfold oddCoreGraphDensity maassCovariantEnergy maassCovariantValue oddCovariantDirection
  simp only [Complex.one_re, Complex.I_re, Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_mul]

theorem continuous_oddCoreGraphDensity (f : OddSmoothCompactCore) : Continuous (oddCoreGraphDensity f) := by
  simp_rw [oddCoreGraphDensity_eq]
  exact (((oddCovariantDirection_continuous 1 (Complex.I / 4) f).norm.pow 2).add
    ((oddCovariantDirection_continuous Complex.I 0 f).norm.pow 2)).add ((oddCore_continuous f).norm.pow 2)

private theorem lintegral_sl_translate (g : SL(2, ℤ)) (S : Set ℍ) (D : ℍ → ℝ≥0∞) :
    (∫⁻ z in S, D (g • z)) = ∫⁻ z in translate g S, D z := by
  have hMeasure : MeasurePreserving (fun z : ℍ => g • z) (volume : Measure ℍ) volume :=
    measurePreserving_smul (g : GL (Fin 2) ℝ) volume
  have hEmb : MeasurableEmbedding (fun z : ℍ => g • z) :=
    measurableEmbedding_const_smul (g : GL (Fin 2) ℝ)
  exact hMeasure.setLIntegral_comp_emb hEmb D S

theorem lintegral_levelFourCuspTail_le_chartMass (f : OddSmoothCompactCore) {T : ℝ} (hT : 2 < T) :
    (∫⁻ z in levelFourCuspTail T, ENNReal.ofReal (‖(f : ℂ → ℂ) z‖ ^ 2)) ≤
      ∫⁻ z in standardCuspTail T, ENNReal.ofReal (oddCosetChartMassAt (f : ℂ → ℂ) z) := by
  let H := CongruenceSubgroup.Gamma0 4
  letI := rightCosetFintype H
  let S := standardCuspTail T
  let M (z : ℍ) := ENNReal.ofReal (‖(f : ℂ → ℂ) z‖ ^ 2)
  let A (q : levelFourRightCoset) (z : ℍ) := M (cellRepresentative H q • z)
  have hM : Measurable M := ENNReal.measurable_ofReal.comp ((oddCore_continuous f).norm.pow 2).measurable
  have hA (q : levelFourRightCoset) : Measurable (A q) :=
    hM.comp (measurable_const_smul (cellRepresentative H q : GL (Fin 2) ℝ))
  have hMass (z : ℍ) : ENNReal.ofReal (oddCosetChartMassAt (f : ℂ → ℂ) z) = ∑ q, A q z := by
    unfold oddCosetChartMassAt
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    simp only [A, M, H, norm_oddCosetChart]
  calc
    _ ≤ ∑' q : levelFourRightCoset, ∫⁻ z in translate (cellRepresentative H q) S, M z := by
      rw [levelFourCuspTail_eq_cosetCells hT]
      exact lintegral_iUnion_le _ _
    _ = ∑ q : levelFourRightCoset, ∫⁻ z in S, A q z := by
      rw [tsum_fintype]
      exact Finset.sum_congr rfl (fun q _ => (lintegral_sl_translate (cellRepresentative H q) S M).symm)
    _ = _ := by simp_rw [hMass]; exact (lintegral_finsetSum _ (fun q _ => hA q)).symm

theorem lintegral_oddChartEnergy_le_levelFour (f : OddSmoothCompactCore) :
    (∫⁻ z in ModularGroup.fd, ENNReal.ofReal (oddCosetChartTotalEnergy f z)) ≤
      letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
      (Fintype.card levelFourRightCoset : ℝ≥0∞) *
        ∫⁻ z in levelFourCells, ENNReal.ofReal (oddCoreGraphDensity f z) := by
  let H := CongruenceSubgroup.Gamma0 4
  letI := rightCosetFintype H
  let D (z : ℍ) := ENNReal.ofReal (oddCoreGraphDensity f z)
  let A (q : levelFourRightCoset) (z : ℍ) := D (cellRepresentative H q • z)
  have hD : Measurable D :=
    ENNReal.measurable_ofReal.comp (continuous_oddCoreGraphDensity f).measurable
  have hA (q : levelFourRightCoset) : Measurable (A q) :=
    hD.comp (measurable_const_smul (cellRepresentative H q : GL (Fin 2) ℝ))
  have hEnergy (z : ℍ) : ENNReal.ofReal (oddCosetChartTotalEnergy f z) = ∑ q, A q z := by
    unfold oddCosetChartTotalEnergy oddCosetChartEnergyAt oddCosetChartMassAt
    rw [← Finset.sum_add_distrib, ENNReal.ofReal_sum_of_nonneg]
    · simp only [A, D, H, oddCoreGraphDensity, energy_oddCosetPullback, norm_oddCosetChart]
    · intro q _
      rw [energy_oddCosetPullback, norm_oddCosetChart]
      exact oddCoreGraphDensity_nonneg _ _
  calc
    _ = ∑ q : levelFourRightCoset, ∫⁻ z in ModularGroup.fd, A q z := by
      simp_rw [hEnergy]
      exact lintegral_finsetSum _ (fun q _ => hA q)
    _ ≤ ∑ _ : levelFourRightCoset, ∫⁻ z in levelFourCells, D z := by
      apply Finset.sum_le_sum
      intro q _
      rw [show (∫⁻ z in ModularGroup.fd, A q z) =
        ∫⁻ z in translate (cellRepresentative H q) ModularGroup.fd, D z from lintegral_sl_translate _ _ _]
      exact lintegral_mono_set (fun z hz => mem_iUnion.mpr ⟨q, hz⟩)
    _ = _ := by simp [D, Finset.sum_const, nsmul_eq_mul]

theorem lintegral_levelFourCuspTail_le_graphDensity (f : OddSmoothCompactCore) {T : ℝ} (hT : 2 < T) :
    (∫⁻ z in levelFourCuspTail T, ENNReal.ofReal (‖(f : ℂ → ℂ) z‖ ^ 2)) ≤
      letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
      ENNReal.ofReal (oddCuspTailConstant / T ^ 2) * (Fintype.card levelFourRightCoset : ℝ≥0∞) *
        ∫⁻ z in levelFourCells, ENNReal.ofReal (oddCoreGraphDensity f z) := by
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  have hT' : 1 ≤ T := by linarith
  refine (lintegral_levelFourCuspTail_le_chartMass f hT).trans
    ((oddCosetChart_lintegral_cusp_tail_le f hT').trans ?_)
  rw [mul_assoc]
  exact mul_le_mul_left' (lintegral_oddChartEnergy_le_levelFour f) _

end
end ManuscriptAudit.Paper8OddMaassLevelFourTail

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassLevelFourTail.lintegral_levelFourCuspTail_le_graphDensity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
