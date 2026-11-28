import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareUnfold

/-! The first Fourier coefficient of the absolutely convergent cross-cusp series equals its full arithmetic modulus expansion. -/

namespace ManuscriptAudit.Paper8OddCrossFourierExpansion

open Filter Set MeasureTheory UpperHalfPlane MaassLaplacian
open Paper8OddCrossCuspNormalization Paper8OddCrossCuspCutoff Paper8OddCrossCuspActualMultiplier
open Paper8OddCrossCuspPhase Paper8OddCrossScaledRows Paper8OddCrossPoincareKernel
open Paper8OddCrossPoincareHeight Paper8OddCrossPoincareConvergence Paper8OddCrossPoincareTranslate
open Paper8OddCrossPoincareRowKernel Paper8OddCrossPoincareUnfold

noncomputable section

private theorem exponentialPhase_real_norm (t : ℝ) : ‖exponentialPhase (t : ℂ)‖ = 1 := by
  rw [exponentialPhase, Complex.norm_exp]
  norm_num [Complex.mul_re, Complex.mul_im]

private theorem row_fourier_continuous (s : ℂ) {y : ℝ} (hy : 0 < y) (i : CrossIndex) :
    Continuous (fun x : ℝ => oddCrossFourierTerm s (pointAtHeight x hy) i) := by
  rcases i with ⟨D, A, n⟩
  let c : ℝ := 2 * ((D + 1 : ℕ) : ℝ)
  let a := crossEntry (D + 1) (A.matrix 0 0) (A.matrix 1 1)
  let b := crossRowShift A
  have hC : Continuous (fun x : ℝ => a * crossRealKernel s y c ((n : ℝ) + x + b)) :=
    continuous_const.mul ((crossRealKernel_continuous s hy (by dsimp only [c]; positivity)).comp
      ((continuous_const.add continuous_id).add continuous_const))
  have hEq : (fun x : ℝ => oddCrossFourierTerm s (pointAtHeight x hy) ⟨D, A, n⟩) =
      (fun x : ℝ => a * crossRealKernel s y c ((n : ℝ) + x + b)) := by
    funext x
    rw [oddCrossFourierTerm_translate, oddCrossFourierTerm_row_kernel, translatePoint_re, pointAtHeight_re]
    have hIm : (translatePoint n (pointAtHeight x hy)).im = y := complexPoint_im _ _
    rw [hIm]
  rwa [hEq]

theorem odd_cross_fourier_expansion (s : ℂ) (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..(1 : ℝ), ∑' i : CrossIndex, oddCrossFourierTerm s (pointAtHeight x hy) i) =
      ∑' D : ℕ, crossSum (Nat.succ_pos D) *
        ∫ u : ℝ, crossRealKernel s y (2 * ((D + 1 : ℕ) : ℝ)) u := by
  let U := Ioc (0 : ℝ) 1
  let μ := (volume : Measure ℝ).restrict U
  let f (i : CrossIndex) (x : ℝ) := oddCrossFourierTerm s (pointAtHeight x hy) i
  let J (i : CrossIndex) := ∫ x, f i x ∂μ
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, U, Real.volume_Ioc]⟩
  obtain ⟨M, hM, hBound⟩ := exists_summable_crossMajorant_on_unit_strip s hs hy
  have hNorm (i : CrossIndex) : ∀ᵐ x ∂μ, ‖f i x‖ ≤ M i :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall (fun x hx => by
      have hx0 : 0 ≤ x := hx.1.le
      have hx1 : x ≤ 1 := hx.2
      have hre : |(pointAtHeight x hy).re| ≤ 1 := by
        rw [pointAtHeight_re, abs_of_nonneg hx0]
        exact hx1
      have h := hBound (pointAtHeight x hy) (complexPoint_im x y) hre i
      unfold f oddCrossFourierTerm
      rw [norm_mul, exponentialPhase_real_norm, mul_one]
      exact h))
  have hConst (i : CrossIndex) : Integrable (fun _ : ℝ => M i) μ := integrable_const _
  have hInt (i : CrossIndex) : Integrable (f i) μ :=
    (hConst i).mono' (row_fourier_continuous s hy i).aestronglyMeasurable (hNorm i)
  have hNormInt (i : CrossIndex) : (∫ x, ‖f i x‖ ∂μ) ≤ M i := by
    have h := integral_mono_ae (hInt i).norm (hConst i) (hNorm i)
    simpa [μ, U, Measure.real_def, Real.volume_Ioc] using h
  have hIntNormSum : Summable (fun i : CrossIndex => ∫ x, ‖f i x‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hNormInt hM
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
      _ = ∑' n : ℤ, ∑ A : CrossRow (D + 1), J ⟨D, A, n⟩ := by
        rw [hSwapped.tsum_prod]
        simp only [swap, Equiv.prodComm_apply, tsum_fintype]
      _ = _ := by
        have h := (hasSum_oddCross_modulus_fourier hOdd s (by linarith) hy).tsum_eq
        simp only [intervalIntegral.integral_of_le zero_le_one] at h
        exact h
  · letI : IsEmpty (CrossRow (D + 1)) := ⟨fun A => hOdd (crossRow_odd A)⟩
    simp [crossSum, hOdd]

end
end ManuscriptAudit.Paper8OddCrossFourierExpansion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossFourierExpansion.odd_cross_fourier_expansion
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
