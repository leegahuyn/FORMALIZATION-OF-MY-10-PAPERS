import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddAllCuspMonodromy

/-! A direct horizontal Poincaré inequality for the nontrivial period-four cusp character. -/

namespace ManuscriptAudit.Paper8OddCuspPoincare

open MeasureTheory Set
open Paper8EtaCriticalOddVanishing Paper8OddAllCuspMonodromy
open scoped MatrixGroups

noncomputable section

private theorem interval_square_mean_le (f : ℝ → ℝ) (hF : Continuous f) (x : ℝ) :
    (∫ t in x..x + 4, f t) ^ 2 ≤ 4 * ∫ t in x..x + 4, f t ^ 2 := by
  let A := ∫ t in x..x + 4, f t
  let B := ∫ t in x..x + 4, f t ^ 2
  let p : ℝ := A / 4
  have hab : x ≤ x + 4 := by linarith
  have h1 : IntervalIntegrable f volume x (x + 4) := hF.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => f t ^ 2) volume x (x + 4) :=
    (hF.pow 2).intervalIntegrable _ _
  have hI : (∫ t in x..x + 4, (f t - p) ^ 2) = B - 2 * p * A + 4 * p ^ 2 := by
    calc
      _ = ∫ t in x..x + 4, (f t ^ 2 - (2 * p) * f t) + p ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (h2.sub (h1.const_mul _)) (continuous_const.intervalIntegrable _ _),
          intervalIntegral.integral_sub h2 (h1.const_mul _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul]
        change B - 2 * p * A + (x + 4 - x) * p ^ 2 = _
        ring
  have hNN : 0 ≤ ∫ t in x..x + 4, (f t - p) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg (f t - p))
  rw [hI] at hNN
  dsimp only [p] at hNN
  change A ^ 2 ≤ 4 * B
  nlinarith only [hNN]

theorem floquet_point_norm_sq_le {q : ℂ} (hq : q ≠ 1) {f f' : ℝ → ℂ}
    (hDeriv : ∀ t : ℝ, HasDerivAt f (f' t) t) (hCont : Continuous f')
    (hFloquet : ∀ t : ℝ, f (t + 4) = q * f t) (x : ℝ) :
    ‖f x‖ ^ 2 ≤ (4 * ∫ t in x..x + 4, ‖f' t‖ ^ 2) / ‖q - 1‖ ^ 2 := by
  let A := ∫ t in x..x + 4, ‖f' t‖
  let B := ∫ t in x..x + 4, ‖f' t‖ ^ 2
  let Q := ‖q - 1‖
  have hQ : 0 < Q := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
  have hab : x ≤ x + 4 := by linarith
  have hFTC : (∫ t in x..x + 4, f' t) = f (x + 4) - f x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hDeriv t) (hCont.intervalIntegrable _ _)
  have hLe : Q * ‖f x‖ ≤ A := by
    rw [show Q = ‖q - 1‖ from rfl, ← norm_mul, sub_mul, one_mul, ← hFloquet, ← hFTC]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg hab (fun t _ => norm_nonneg (f' t))
  have hProd : 0 ≤ Q * ‖f x‖ := mul_nonneg hQ.le (norm_nonneg _)
  have hSq : (Q * ‖f x‖) ^ 2 ≤ A ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hLe) (add_nonneg hA hProd)]
  have hMean : A ^ 2 ≤ 4 * B := interval_square_mean_le (fun t => ‖f' t‖) hCont.norm x
  change ‖f x‖ ^ 2 ≤ (4 * B) / Q ^ 2
  apply (le_div_iff₀ (sq_pos_of_pos hQ)).2
  nlinarith only [hSq.trans hMean]

theorem floquet_strip_norm_sq_le {q : ℂ} (hq : q ≠ 1) {f f' : ℝ → ℂ}
    (hDeriv : ∀ t : ℝ, HasDerivAt f (f' t) t) (hCont : Continuous f')
    (hFloquet : ∀ t : ℝ, f (t + 4) = q * f t) :
    (∫ t in (0 : ℝ)..4, ‖f t‖ ^ 2) ≤
      (16 * ∫ t in (0 : ℝ)..8, ‖f' t‖ ^ 2) / ‖q - 1‖ ^ 2 := by
  let B := ∫ t in (0 : ℝ)..8, ‖f' t‖ ^ 2
  let C := (4 * B) / ‖q - 1‖ ^ 2
  have hF : Continuous f := (show Differentiable ℝ f from fun t => (hDeriv t).differentiableAt).continuous
  have hB : IntervalIntegrable (fun t => ‖f' t‖ ^ 2) volume 0 8 := (hCont.norm.pow 2).intervalIntegrable _ _
  have hQ : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
  have hBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) : ‖f t‖ ^ 2 ≤ C := by
    have hi : (∫ u in t..t + 4, ‖f' u‖ ^ 2) ≤ B :=
      intervalIntegral.integral_mono_interval ht.1 (by linarith) (by linarith [ht.2])
        (Filter.Eventually.of_forall (fun u => sq_nonneg ‖f' u‖)) hB
    refine (floquet_point_norm_sq_le hq hDeriv hCont hFloquet t).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) (sq_nonneg _)
  calc
    _ ≤ ∫ t in (0 : ℝ)..4, C := intervalIntegral.integral_mono_on (by norm_num)
      ((hF.norm.pow 2).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hBound
    _ = _ := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      unfold C B
      ring

theorem actual_cusp_horizontal_energy {F : ℂ → ℂ} (hLaw : OddMaassLaw F)
    (g : SL(2, ℤ)) {y : ℝ} (hy : 0 < y) {D : ℝ → ℂ}
    (hDeriv : ∀ x : ℝ, HasDerivAt (fun t => cuspHorizontalProfile F g t y) (D x) x)
    (hCont : Continuous D) :
    (∫ t in (0 : ℝ)..4, ‖cuspHorizontalProfile F g t y‖ ^ 2) ≤
      (16 * ∫ t in (0 : ℝ)..8, ‖D t‖ ^ 2) / ‖periodFourPhase - 1‖ ^ 2 :=
  floquet_strip_norm_sq_le periodFourPhase_ne_one hDeriv hCont
    (fun t => cuspHorizontalProfile_floquet hLaw g t y hy)

end
end ManuscriptAudit.Paper8OddCuspPoincare

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCuspPoincare.actual_cusp_horizontal_energy
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
