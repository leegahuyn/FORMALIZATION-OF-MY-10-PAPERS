import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.Prod
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCuspPoincare

/-! Uniform hyperbolic cusp-tail control for the actual odd multiplier. -/

namespace ManuscriptAudit.Paper8OddCuspEnergyTail

open Filter MeasureTheory Set
open Paper8EtaCriticalOddVanishing Paper8OddAllCuspMonodromy Paper8OddCuspPoincare
open scoped MatrixGroups

noncomputable section

theorem actual_cusp_tail_energy_le {F : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (g : SL(2, ℤ)) {T : ℝ} (hT : 0 < T) (D : ℝ → ℝ → ℂ)
    (hMeas : Measurable (fun p : ℝ × ℝ => cuspHorizontalProfile F g p.1 p.2))
    (hDeriv : ∀ y, T < y → ∀ x : ℝ,
      HasDerivAt (fun t => cuspHorizontalProfile F g t y) (D x y) x)
    (hCont : ∀ y, T < y → Continuous (fun x => D x y))
    (hEnergy : IntegrableOn (fun y => ∫ x in (0 : ℝ)..8, ‖D x y‖ ^ 2) (Ioi T)) :
    (∫ y in Ioi T, (∫ x in (0 : ℝ)..4, ‖cuspHorizontalProfile F g x y‖ ^ 2) / y ^ 2) ≤
      (16 / (‖periodFourPhase - 1‖ ^ 2 * T ^ 2)) *
        ∫ y in Ioi T, ∫ x in (0 : ℝ)..8, ‖D x y‖ ^ 2 := by
  let A (y : ℝ) := ∫ x in (0 : ℝ)..4, ‖cuspHorizontalProfile F g x y‖ ^ 2
  let B (y : ℝ) := ∫ x in (0 : ℝ)..8, ‖D x y‖ ^ 2
  let Q := ‖periodFourPhase - 1‖ ^ 2
  let C := 16 / (Q * T ^ 2)
  let μ := (volume : Measure ℝ).restrict (Ioi T)
  have hQ : 0 < Q := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr periodFourPhase_ne_one))
  have hMeasure : StronglyMeasurable A := by
    unfold A
    simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)]
    exact (hMeas.norm.pow_const 2).stronglyMeasurable.integral_prod_left'
  have hNonneg (y : ℝ) : 0 ≤ A y / y ^ 2 := by
    have hA : 0 ≤ A y := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
    exact div_nonneg hA (sq_nonneg _)
  have hBound (y : ℝ) (hy : T < y) : A y / y ^ 2 ≤ C * B y := by
    have hB : 0 ≤ B y := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
    have hy0 := hT.trans hy
    have hSq : T ^ 2 ≤ y ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hy.le) (show 0 ≤ y + T by positivity)]
    have h := actual_cusp_horizontal_energy hLaw g hy0 (hDeriv y hy) (hCont y hy)
    change A y ≤ (16 * B y) / Q at h
    calc
      _ ≤ ((16 * B y) / Q) / y ^ 2 := div_le_div_of_nonneg_right h (sq_nonneg _)
      _ ≤ ((16 * B y) / Q) / T ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hT) hSq
      _ = _ := by
        dsimp only [C]
        rw [div_div]
        ring
  have hBoundAE : ∀ᵐ y ∂μ, ‖A y / y ^ 2‖ ≤ C * B y :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg y)]
      exact hBound y hy))
  have hIntB : Integrable (fun y => C * B y) μ := hEnergy.const_mul C
  have hIntA : Integrable (fun y => A y / y ^ 2) μ :=
    hIntB.mono' (hMeasure.measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable hBoundAE
  have hLeAE : ∀ᵐ y ∂μ, A y / y ^ 2 ≤ C * B y := by
    filter_upwards [hBoundAE] with y hy
    rwa [Real.norm_eq_abs, abs_of_nonneg (hNonneg y)] at hy
  change (∫ y, A y / y ^ 2 ∂μ) ≤ C * ∫ y, B y ∂μ
  rw [← integral_const_mul]
  exact integral_mono_ae hIntA hIntB hLeAE

end
end ManuscriptAudit.Paper8OddCuspEnergyTail

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCuspEnergyTail.actual_cusp_tail_energy_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
