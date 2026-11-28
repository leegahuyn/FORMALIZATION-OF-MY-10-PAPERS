import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassGridApproximation
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddMaassCompactCriterion
import PrimalitySheafVerification.ManuscriptAudit.Paper8UniformIntervalGrid

/-! Compactness of the actual odd Maass energy inclusion and variational resolvent. -/

namespace ManuscriptAudit.Paper8OddMaassCompactResolvent

open Paper8OddMaassHilbertCore Paper8OddMaassEnergyCompletion Paper8OddMaassCompactCriterion
open Paper8OddMaassGridApproximation Paper8OddMaassCuspTailEstimate Paper8ModularCoreRectangle
open Paper8OddCosetChartTransition Paper8UniformIntervalGrid FiniteIndexWeightZeroCosets
open scoped ENNReal

noncomputable section

private def realCosetCount : ℝ :=
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  (Fintype.card levelFourRightCoset : ℝ)

private theorem realCosetCount_nonneg : 0 ≤ realCosetCount := by
  unfold realCosetCount
  positivity

private def realTailCoefficient : ℝ := oddCuspTailConstant * realCosetCount

private def realGridCoefficient (T : ℝ) : ℝ :=
  ((coreMinimumHeight ^ 2)⁻¹) * 2 * ((3 / coreMinimumHeight ^ 2) * T ^ 2 * 2 * realCosetCount)

private theorem realTailCoefficient_nonneg : 0 ≤ realTailCoefficient :=
  mul_nonneg oddCuspTailConstant_nonneg realCosetCount_nonneg

private theorem realGridCoefficient_nonneg (T : ℝ) : 0 ≤ realGridCoefficient T := by
  unfold realGridCoefficient
  positivity

private theorem oddTailApproximationCoefficient_eq (T : ℝ) :
    oddTailApproximationCoefficient T = ENNReal.ofReal (realTailCoefficient / T ^ 2) := by
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  have hReal : realTailCoefficient / T ^ 2 =
      (oddCuspTailConstant / T ^ 2) * realCosetCount := by
    unfold realTailCoefficient
    ring
  rw [hReal, ENNReal.ofReal_mul (div_nonneg oddCuspTailConstant_nonneg (sq_nonneg _))]
  unfold oddTailApproximationCoefficient realCosetCount
  rw [ENNReal.ofReal_natCast]

private theorem oddGridApproximationCoefficient_eq (T δ : ℝ) :
    oddGridApproximationCoefficient T δ = ENNReal.ofReal (realGridCoefficient T * δ ^ 2) := by
  let A : ℝ := (coreMinimumHeight ^ 2)⁻¹
  let B : ℝ := 2 * δ ^ 2
  let C : ℝ := 3 / coreMinimumHeight ^ 2
  have hA : 0 ≤ A := inv_nonneg.mpr (sq_nonneg _)
  have hB : 0 ≤ B := by unfold B; positivity
  have hC : 0 ≤ C := div_nonneg (by norm_num) (sq_nonneg _)
  have hReal : realGridCoefficient T * δ ^ 2 = (A * B) * (((C * T ^ 2) * 2) * realCosetCount) := by
    unfold realGridCoefficient A B C
    ring
  rw [hReal, ENNReal.ofReal_mul (mul_nonneg hA hB), ENNReal.ofReal_mul hA,
    ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC (sq_nonneg _)) (by norm_num)),
    ENNReal.ofReal_mul (mul_nonneg hC (sq_nonneg _)), ENNReal.ofReal_mul hC]
  have hb : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [hb]
  unfold oddGridApproximationCoefficient realCosetCount
  rw [ENNReal.ofReal_natCast]

private theorem exists_small_oddMaass_approximation_coefficients {ε : ℝ} (hε : 0 < ε) :
    ∃ T δ : ℝ, 2 < T ∧ 0 < δ ∧
      oddTailApproximationCoefficient T + oddGridApproximationCoefficient T δ ≤ ENNReal.ofReal (ε ^ 2) := by
  let T : ℝ := max 3 (Real.sqrt (2 * realTailCoefficient) / ε)
  have hT : 2 < T := (by norm_num : (2 : ℝ) < 3).trans_le (le_max_left _ _)
  have hT₀ : 0 < T := by linarith
  let R := Real.sqrt (2 * realGridCoefficient T + 1)
  have hR₀ : 0 < 2 * realGridCoefficient T + 1 := by linarith [realGridCoefficient_nonneg T]
  have hR : 0 < R := Real.sqrt_pos.2 hR₀
  let δ := ε / R
  have hδ : 0 < δ := div_pos hε hR
  have hTail : realTailCoefficient / T ^ 2 ≤ ε ^ 2 / 2 := by
    have hS : Real.sqrt (2 * realTailCoefficient) ≤ ε * T := by
      have hS := (div_le_iff₀ hε).mp (le_max_right (3 : ℝ) (Real.sqrt (2 * realTailCoefficient) / ε))
      simpa only [T, mul_comm T ε] using hS
    have hSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hS 2
    rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) realTailCoefficient_nonneg), mul_pow] at hSq
    apply (div_le_iff₀ (sq_pos_of_pos hT₀)).mpr
    nlinarith only [hSq]
  have hGrid : realGridCoefficient T * δ ^ 2 ≤ ε ^ 2 / 2 := by
    have hs : R ^ 2 = 2 * realGridCoefficient T + 1 := Real.sq_sqrt hR₀.le
    unfold δ
    rw [div_pow, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    rw [hs]
    nlinarith only [sq_nonneg ε]
  refine ⟨T, δ, hT, hδ, ?_⟩
  rw [oddTailApproximationCoefficient_eq, oddGridApproximationCoefficient_eq,
    ← ENNReal.ofReal_add (div_nonneg realTailCoefficient_nonneg (sq_nonneg _))
      (mul_nonneg (realGridCoefficient_nonneg T) (sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (by linarith only [hTail, hGrid])

theorem oddMaass_smooth_core_finite_cell_approx (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Submodule ℂ OddMaassL2, FiniteDimensional ℂ K ∧
      ∀ f : OddSmoothCompactCore, ∃ k : K, ‖oddCoreVector f - (k : OddMaassL2)‖ ≤ ε * ‖oddCoreEnergyGraph f‖ := by
  obtain ⟨T, δ, hT, hδ, hSmall⟩ := exists_small_oddMaass_approximation_coefficients hε
  have hB : coreMinimumHeight < T := by
    have h : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).2 (by norm_num)
    unfold coreMinimumHeight
    linarith
  have hWidth : (-(1 / 2) : ℝ) < 1 / 2 := by norm_num
  obtain ⟨n, hn, hXδ⟩ := exists_grid_mesh_le hWidth hδ
  obtain ⟨m, hm, hYδ⟩ := exists_grid_mesh_le hB hδ
  obtain ⟨K, hK, hApprox⟩ := exists_oddMaass_gridApprox hn hm hT
    (gridEndpoint (-(1 / 2)) (1 / 2) n) (gridEndpoint coreMinimumHeight T m)
    (gridEndpoint_strictMono hWidth hn) (gridEndpoint_strictMono hB hm)
    (gridEndpoint_zero _ _ _) (gridEndpoint_last _ _ hn)
    (gridEndpoint_zero _ _ _) (gridEndpoint_last _ _ hm)
    (fun i _ => hXδ i) (fun j _ => hYδ j)
  refine ⟨K, hK, ?_⟩
  intro f
  obtain ⟨v, hv, hE⟩ := hApprox f
  refine ⟨⟨v, hv⟩, ?_⟩
  have hSq := hE.trans (mul_le_mul_right' hSmall (ENNReal.ofReal (‖oddCoreEnergyGraph f‖ ^ 2)))
  rw [← ENNReal.ofReal_mul (sq_nonneg ε), ← mul_pow] at hSq
  have h := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hSq
  exact by
    simpa only [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hε.le (norm_nonneg _))] using sq_le_sq.mp h

theorem oddMaassEnergyInclusion_compact : IsCompactOperator oddMaassEnergyInclusion :=
  oddMaassEnergyInclusion_compact_of_smooth_cell_approx oddMaass_smooth_core_finite_cell_approx

theorem oddMaassVariationalResolvent_compact : IsCompactOperator oddMaassVariationalResolvent :=
  oddMaassVariationalResolvent_compact_of_smooth_cell_approx oddMaass_smooth_core_finite_cell_approx

end
end ManuscriptAudit.Paper8OddMaassCompactResolvent

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassCompactResolvent.oddMaassVariationalResolvent_compact
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
