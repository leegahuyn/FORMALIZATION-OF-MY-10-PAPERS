import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossLocalizedRows
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossFirstCoefficient

/-! The height-truncated cross Fourier coefficient is genuinely nonzero. -/

namespace ManuscriptAudit.Paper8OddCrossLocalizedFourier

open Filter Set MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8OddCrossCuspNormalization Paper8OddCrossCuspCutoff Paper8OddCrossCuspActualMultiplier
open Paper8OddCrossCuspPhase Paper8OddCrossScaledRows Paper8OddCrossPoincareKernel
open Paper8OddCrossPoincareHeight Paper8OddCrossPoincareConvergence Paper8OddCrossPoincareUnfold
open Paper8OddCrossLocalizedKernel Paper8OddCrossLocalizedRows Paper8OddCrossFirstCoefficient

noncomputable section

private theorem hasSum_oddCrossHeightCutoff_modulus_fourier {D : ℕ} (hOdd : Odd (D + 1))
    {q y : ℝ} (hq : 0 < q) (hy : 0 < y) :
    letI := analyticCrossFintype (Nat.succ_pos D) hOdd
    HasSum (fun n : ℤ => ∑ A : CrossRow (D + 1), ∫ x in (0 : ℝ)..(1 : ℝ),
      oddCrossHeightCutoffFourierTerm q (pointAtHeight x hy) ⟨D, A, n⟩)
      (crossSum (Nat.succ_pos D) *
      ∫ u : ℝ, crossHeightCutoffKernel q y (2 * ((D + 1 : ℕ) : ℝ)) u) := by
  letI := analyticCrossFintype (Nat.succ_pos D) hOdd
  let C (A : CrossRow (D + 1)) := crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1)
  let K := ∫ u : ℝ, crossHeightCutoffKernel q y (2 * ((D + 1 : ℕ) : ℝ)) u
  have hSum : crossSum (Nat.succ_pos D) = ∑ A : CrossRow (D + 1), C A := by
    rw [crossSum_eq_analytic (Nat.succ_pos D) hOdd (pointAtHeight 0 hy)]
    exact Finset.sum_congr rfl (fun A _ => analyticCrossEntry_eq (Nat.succ_pos D) A _)
  have hRows : HasSum (fun n : ℤ => ∑ A : CrossRow (D + 1), ∫ x in (0 : ℝ)..(1 : ℝ),
      oddCrossHeightCutoffFourierTerm q (pointAtHeight x hy) ⟨D, A, n⟩)
      (∑ A : CrossRow (D + 1), C A * K) := by
    apply hasSum_sum
    intro A _
    exact hasSum_oddCrossHeightCutoff_row_fourier A hq hy
  rw [← Finset.sum_mul, ← hSum] at hRows
  exact hRows

private theorem exponentialPhase_real_norm (t : ℝ) : ‖exponentialPhase (t : ℂ)‖ = 1 := by
  rw [exponentialPhase, Complex.norm_exp]
  norm_num [Complex.mul_re, Complex.mul_im]

theorem odd_cross_height_cutoff_fourier_expansion {q y : ℝ} (hq : 0 < q) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..(1 : ℝ), ∑' i : CrossIndex,
      oddCrossHeightCutoffFourierTerm q (pointAtHeight x hy) i) =
      ∑' D : ℕ, crossSum (Nat.succ_pos D) *
        ∫ u : ℝ, crossHeightCutoffKernel q y (2 * ((D + 1 : ℕ) : ℝ)) u := by
  let U := Ioc (0 : ℝ) 1
  let μ := (volume : Measure ℝ).restrict U
  let f (i : CrossIndex) (x : ℝ) := oddCrossHeightCutoffFourierTerm q (pointAtHeight x hy) i
  let J (i : CrossIndex) := ∫ x, f i x ∂μ
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, U, Real.volume_Ioc]⟩
  obtain ⟨M, hM, hBound⟩ := exists_summable_crossMajorant_on_unit_strip (2 : ℂ) (by norm_num) hy
  let N (i : CrossIndex) := (q ^ 2)⁻¹ * M i
  have hN : Summable N := hM.mul_left _
  have hNorm (i : CrossIndex) : ∀ᵐ x ∂μ, ‖f i x‖ ≤ N i := by
    filter_upwards [ae_restrict_mem (show MeasurableSet U from measurableSet_Ioc)] with x hx
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : x ≤ 1 := hx.2
    have hre : |(pointAtHeight x hy).re| ≤ 1 := by
      rw [pointAtHeight_re, abs_of_nonneg hx0]
      exact hx1
    have hTerm := hBound (pointAtHeight x hy) (pointAtHeight_im x hy) hre i
    have hFull : ‖oddCrossFourierTerm 2 (pointAtHeight x hy) i‖ ≤ M i := by
      unfold oddCrossFourierTerm
      rw [norm_mul, exponentialPhase_real_norm, mul_one]
      exact hTerm
    exact (norm_oddCrossHeightCutoffFourierTerm_le hq _ i).trans
      (mul_le_mul_of_nonneg_left hFull (by positivity))
  have hConst (i : CrossIndex) : Integrable (fun _ : ℝ => N i) μ := integrable_const _
  have hInt (i : CrossIndex) : Integrable (f i) μ :=
    (hConst i).mono' (oddCrossHeightCutoffFourierTerm_measurable q hy i).aestronglyMeasurable (hNorm i)
  have hNormInt (i : CrossIndex) : (∫ x, ‖f i x‖ ∂μ) ≤ N i := by
    have h := integral_mono_ae (hInt i).norm (hConst i) (hNorm i)
    simpa [μ, U, Measure.real_def, Real.volume_Ioc] using h
  have hIntNormSum : Summable (fun i : CrossIndex => ∫ x, ‖f i x‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hNormInt hN
  have hIntSum : HasSum J (∫ x, ∑' i : CrossIndex, f i x ∂μ) :=
    hasSum_integral_of_summable_integral_norm hInt hIntNormSum
  rw [intervalIntegral.integral_of_le zero_le_one]
  change (∫ x, ∑' i : CrossIndex, f i x ∂μ) = _
  rw [← hIntSum.tsum_eq, hIntSum.summable.tsum_sigma]
  apply tsum_congr
  intro D
  by_cases hOdd : Odd (D + 1)
  · letI := analyticCrossFintype (Nat.succ_pos D) hOdd
    let swap := Equiv.prodComm ℤ (CrossRow (D + 1))
    have hFiber := hIntSum.summable.sigma_factor D
    have hSwapped : Summable (fun p : ℤ × CrossRow (D + 1) => J ⟨D, swap p⟩) :=
      hFiber.comp_injective swap.injective
    calc
      _ = ∑' p : ℤ × CrossRow (D + 1), J ⟨D, swap p⟩ :=
        (swap.tsum_eq (fun p => J ⟨D, p⟩)).symm
      _ = ∑' n : ℤ, ∑ A : CrossRow (D + 1), J ⟨D, swap (n, A)⟩ := by
        rw [hSwapped.tsum_prod]
        simp only [tsum_fintype]
      _ = _ := by
        have h := (hasSum_oddCrossHeightCutoff_modulus_fourier hOdd hq hy).tsum_eq
        simp only [intervalIntegral.integral_of_le zero_le_one] at h
        exact h
  · letI : IsEmpty (CrossRow (D + 1)) := ⟨fun A => hOdd (crossRow_odd A)⟩
    simp [crossSum, hOdd]

theorem exists_nonzero_odd_cross_height_cutoff_fourier :
    ∃ q : ℝ, 1 / 16 < q ∧ q < 1 / 4 ∧
      (∫ x in (0 : ℝ)..(1 : ℝ), ∑' i : CrossIndex,
        oddCrossHeightCutoffFourierTerm q (pointAtHeight x (show 0 < (1 : ℝ) by norm_num)) i) ≠ 0 := by
  obtain ⟨q, hqLo, hqHi, hKill, hFirst⟩ := exists_crossHeightCutoff_first_modulus_nonzero
  refine ⟨q, hqLo, hqHi, ?_⟩
  rw [odd_cross_height_cutoff_fourier_expansion ((by norm_num : (0 : ℝ) < 1 / 16).trans hqLo)]
  have hSupport (D : ℕ) (hD : D ∉ ({0} : Finset ℕ)) :
      crossSum (Nat.succ_pos D) * ∫ u : ℝ, crossHeightCutoffKernel q 1 (2 * ((D + 1 : ℕ) : ℝ)) u = 0 := by
    have hD0 : D ≠ 0 := by simpa only [Finset.mem_singleton] using hD
    simp only [hKill (D + 1) (by omega), integral_zero, mul_zero]
  rw [tsum_eq_sum hSupport, Finset.sum_singleton]
  simpa only [zero_add, Nat.cast_one, mul_one, crossSum_one, one_mul] using hFirst

end
end ManuscriptAudit.Paper8OddCrossLocalizedFourier

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossLocalizedFourier.odd_cross_height_cutoff_fourier_expansion,
      ``ManuscriptAudit.Paper8OddCrossLocalizedFourier.exists_nonzero_odd_cross_height_cutoff_fourier] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
