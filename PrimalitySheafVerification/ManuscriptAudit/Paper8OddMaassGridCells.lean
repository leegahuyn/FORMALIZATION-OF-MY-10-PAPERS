import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ModularDomainFiniteVolume
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassCoreDerivativeBound
import PrimalitySheafVerification.ManuscriptAudit.Paper8HyperbolicRectangleIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper8RectangularIntegralMeasure
import PrimalitySheafVerification.ManuscriptAudit.Paper8UniformIntervalGrid

/-! The finite rectangular charts reconstruct approximants on the actual level-four cells. -/

namespace ManuscriptAudit.Paper8OddMaassGridCells

open MeasureTheory Set UpperHalfPlane MaassLaplacian
open Paper8OddMaassHilbertCore Paper8OddMaassLevelFourTail Paper8OddGlobalCutoffEnergy
open Paper8EtaCosetMass Paper8EtaHalfWeightPhase Paper8MaassCovariantGeometry
open Paper8OddCosetChartTransition Paper8OddCosetChartEnergy Paper8OddCosetChartDifferential
open Paper8ModularHeightCutoff Paper8ModularCoreRectangle Paper8ModularCoreIntegral
open Paper8UniformIntervalGrid Paper8HyperbolicRectangleIntegral Paper8OddMaassChartExtension
open Paper8RectangularGridApproximation Paper8RectangularIntegralMeasure Paper8RectangularCellApproximation
open FiniteIndexWeightZeroCosets
open Paper8EtaPeterssonMass (translate)
open scoped ENNReal MatrixGroups

noncomputable section

abbrev OddGridTile (n m : ℕ) := levelFourRightCoset × Fin n × Fin m

def oddGridRepresentative {n m : ℕ} (i : OddGridTile n m) : SL(2, ℤ) :=
  cellRepresentative (CongruenceSubgroup.Gamma0 4) i.1

def oddGridSource {n m : ℕ} (X Y : ℕ → ℝ) (i : OddGridTile n m) : Set ℍ :=
  ModularGroup.fd ∩ upperRectangle (X i.2.1) (X (i.2.1.val + 1)) (Y i.2.2) (Y (i.2.2.val + 1))

def oddGridCell {n m : ℕ} (X Y : ℕ → ℝ) (i : OddGridTile n m) : Set ℍ :=
  translate (oddGridRepresentative i) (oddGridSource X Y i)

theorem measurable_oddGridCell {n m : ℕ} (X Y : ℕ → ℝ) (i : OddGridTile n m) :
    MeasurableSet (oddGridCell X Y i) :=
  (measurableEmbedding_const_smul (oddGridRepresentative i : GL (Fin 2) ℝ)).measurableSet_image.mpr
    (ModularGroup.isClosed_fd.measurableSet.inter (measurable_upperRectangle _ _ _ _))

def oddGridPhase {n m : ℕ} (i : OddGridTile n m) (z : ℍ) : ℂ :=
  negativePhase (oddGridRepresentative i) ((oddGridRepresentative i)⁻¹ • z)

theorem continuous_oddGridPhase {n m : ℕ} (i : OddGridTile n m) : Continuous (oddGridPhase i) := by
  let g : SL(2, ℤ) := (oddGridRepresentative i)⁻¹
  change Continuous (fun z : ℍ => negativePhase (oddGridRepresentative i) (g • z))
  apply (negativePhase_continuous (oddGridRepresentative i)).comp
  simpa only [ModularGroup.sl_moeb] using (continuous_const_smul (g : GL (Fin 2) ℝ))

theorem norm_oddGridPhase {n m : ℕ} (i : OddGridTile n m) (z : ℍ) : ‖oddGridPhase i z‖ = 1 :=
  negativePhase_norm _ _

theorem oddMaassMeasure_finite : IsFiniteMeasure oddMaassMeasure := by
  let H := CongruenceSubgroup.Gamma0 4
  letI := rightCosetFintype H
  refine ⟨?_⟩
  rw [oddMaassMeasure, Measure.restrict_apply_univ, ← setLIntegral_one]
  have hUnion := lintegral_iUnion_le (fun q : RightCoset H => translate (cellRepresentative H q) ModularGroup.fd)
    (fun _ : ℍ => (1 : ℝ≥0∞))
  refine hUnion.trans_lt ?_
  rw [tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro q _
  let g := cellRepresentative H q
  have hP : MeasurePreserving (fun z : ℍ => g • z) (volume : Measure ℍ) volume :=
    measurePreserving_smul (g : GL (Fin 2) ℝ) volume
  have hEmb : MeasurableEmbedding (fun z : ℍ => g • z) :=
    measurableEmbedding_const_smul (g : GL (Fin 2) ℝ)
  have hEq := hP.setLIntegral_comp_emb hEmb (fun _ => (1 : ℝ≥0∞)) ModularGroup.fd
  rw [← show (∫⁻ z in ModularGroup.fd, (1 : ℝ≥0∞)) =
    ∫⁻ z in translate g ModularGroup.fd, (1 : ℝ≥0∞) from hEq, setLIntegral_one]
  exact ModularDomainFiniteVolume.volume_fd_lt_top

theorem levelFour_core_subset_iUnion_grid {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (X Y : ℕ → ℝ) {T : ℝ} (hX₀ : X 0 = -(1 / 2)) (hXn : X n = 1 / 2)
    (hY₀ : Y 0 = coreMinimumHeight) (hYm : Y m = T) :
    levelFourCells \ levelFourCuspTail T ⊆ ⋃ i : OddGridTile n m, oddGridCell X Y i := by
  intro z hz
  obtain ⟨q, u, hu, hzu⟩ := mem_iUnion.mp hz.1
  have hZ : maximumHeight z < T := by
    apply lt_of_not_ge
    intro h
    exact hz.2 ⟨hz.1, h⟩
  have hU : u.im ≤ T := by
    have hA : u.im ≤ maximumHeight u := by
      simpa only [one_smul] using im_smul_le_maximumHeight u 1
    have hI : maximumHeight z = maximumHeight u := by
      rw [← hzu, maximumHeight_invariant]
    exact hA.trans (hI ▸ hZ.le)
  have hRect := modular_fd_truncation_subset_rectangle T (show u ∈ ModularGroup.fd ∩ {z | z.im ≤ T} from ⟨hu, hU⟩)
  have hx : u.re ∈ Icc (X 0) (X n) := by
    rw [hX₀, hXn]
    exact abs_le.mp hRect.1
  have hy : u.im ∈ Icc (Y 0) (Y m) := by
    rw [hY₀, hYm]
    exact ⟨hRect.2.1, hRect.2.2⟩
  obtain ⟨i, hi⟩ := exists_mem_gridInterval hn hx
  obtain ⟨j, hj⟩ := exists_mem_gridInterval hm hy
  exact mem_iUnion.mpr ⟨(q, i, j), u, ⟨hu, hi, hj⟩, hzu⟩

theorem oddGridCell_lintegral_error_le {n m : ℕ} (X Y : ℕ → ℝ)
    (hX : Monotone X) (hY : Monotone Y) (hY₀ : coreMinimumHeight ≤ Y 0)
    (f : OddSmoothCompactCore) (i : OddGridTile n m) :
    (∫⁻ z in oddGridCell X Y i, ENNReal.ofReal (‖(f : ℂ → ℂ) z -
        rectangularCellMean (extendedOddChart f i.1) (X i.2.1) (X (i.2.1.val + 1))
          (Y i.2.2) (Y (i.2.2.val + 1)) * oddGridPhase i z‖ ^ 2)) ≤
      ENNReal.ofReal ((coreMinimumHeight ^ 2)⁻¹) *
        ENNReal.ofReal (gridCellError (extendedOddChart f i.1) (X i.2.1) (X (i.2.1.val + 1))
          (Y i.2.2) (Y (i.2.2.val + 1))) := by
  let g := oddGridRepresentative i
  let a := X i.2.1
  let b := X (i.2.1.val + 1)
  let c := Y i.2.2
  let d := Y (i.2.2.val + 1)
  let A := rectangularCellMean (extendedOddChart f i.1) a b c d
  let D (p : ℝ × ℝ) := ENNReal.ofReal (‖extendedOddChart f i.1 p.1 p.2 - A‖ ^ 2)
  let E (z : ℍ) := ENNReal.ofReal (‖(f : ℂ → ℂ) z - A * oddGridPhase i z‖ ^ 2)
  have hB : coreMinimumHeight ≤ c := hY₀.trans (hY (Nat.zero_le _))
  have hD : Measurable D := ENNReal.measurable_ofReal.comp
    (((continuous_extendedOddChart f i.1).sub continuous_const).norm.pow 2).measurable
  have hS : MeasurableSet (oddGridSource X Y i) :=
    ModularGroup.isClosed_fd.measurableSet.inter (measurable_upperRectangle _ _ _ _)
  have hP : MeasurePreserving (fun z : ℍ => g • z) (volume : Measure ℍ) volume :=
    measurePreserving_smul (g : GL (Fin 2) ℝ) volume
  have hEmb : MeasurableEmbedding (fun z : ℍ => g • z) :=
    measurableEmbedding_const_smul (g : GL (Fin 2) ℝ)
  have hAt (z : ℍ) (hz : z ∈ oddGridSource X Y i) : E (g • z) = D (z.re, z.im) := by
    have hZ : coreMinimumHeight ≤ z.im := hB.trans hz.2.2.1
    have hCoord : coreCoordinatePoint (z.re, z.im) = z := by
      apply UpperHalfPlane.ext
      change complexPoint z.re (max z.im coreMinimumHeight) = (z : ℂ)
      rw [max_eq_left hZ]
      exact z.re_add_im
    have hExt := extendedOddChart_eq_on_core f i.1 (p := (z.re, z.im)) hZ
    rw [hCoord] at hExt
    have hPhase : oddGridPhase i (g • z) = negativePhase g z := by simp only [oddGridPhase, g, inv_smul_smul]
    have hNe : negativePhase g z ≠ 0 := by
      intro h
      have hNorm := negativePhase_norm g z
      simp [h] at hNorm
    have hDiff : (f : ℂ → ℂ) (g • z : ℍ) - A * oddGridPhase i (g • z) =
        negativePhase g z * (extendedOddChart f i.1 z.re z.im - A) := by
      rw [hPhase, hExt, oddCosetPullback, oddMaassPullback_coe]
      change _ = negativePhase g z * ((negativePhase g z)⁻¹ * (f : ℂ → ℂ) (g • z : ℍ) - A)
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hNe, one_mul, mul_comm (negativePhase g z) A]
    change ENNReal.ofReal (‖(f : ℂ → ℂ) (g • z : ℍ) - A * oddGridPhase i (g • z)‖ ^ 2) = _
    rw [hDiff, norm_mul, negativePhase_norm, one_mul] <;> rfl
  calc
    _ = ∫⁻ z in oddGridSource X Y i, E (g • z) :=
      (hP.setLIntegral_comp_emb hEmb E _).symm
    _ = ∫⁻ z in oddGridSource X Y i, D (z.re, z.im) := setLIntegral_congr_fun hS hAt
    _ ≤ ∫⁻ z in upperRectangle a b c d, D (z.re, z.im) := lintegral_mono_set inter_subset_right
    _ ≤ ENNReal.ofReal ((coreMinimumHeight ^ 2)⁻¹) *
        ∫⁻ p : ℝ × ℝ in Icc a b ×ˢ Icc c d, D p :=
      lintegral_upperRectangle_le_euclidean hD coreMinimumHeight_pos hB
    _ = _ := by
      rw [← ofReal_rectangleIntegral_eq_lintegral
        (((continuous_extendedOddChart f i.1).sub continuous_const).norm.pow 2)
        (fun _ _ => sq_nonneg _) (hX (Nat.le_succ _)) (hY (Nat.le_succ _))] <;> rfl

end
end ManuscriptAudit.Paper8OddMaassGridCells

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddMaassGridCells.levelFour_core_subset_iUnion_grid,
      ``ManuscriptAudit.Paper8OddMaassGridCells.oddGridCell_lintegral_error_le] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
