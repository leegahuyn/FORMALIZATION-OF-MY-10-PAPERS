import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Sqrt

/-! The quantitative interval cell-average estimate used in compact Sobolev approximation. -/

namespace ManuscriptAudit.Paper8IntervalCellApproximation

open MeasureTheory Set

noncomputable section

private theorem interval_integral_sq_le (g : ℝ → ℝ) (hg : Continuous g) {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, g t ^ 2 := by
  let L := b - a
  let A := ∫ t in a..b, g t
  let B := ∫ t in a..b, g t ^ 2
  let p := A / L
  have hL : 0 < L := sub_pos.mpr hab
  have hA : IntervalIntegrable g volume a b := hg.intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t => g t ^ 2) volume a b := (hg.pow 2).intervalIntegrable _ _
  have hId : (∫ t in a..b, (g t - p) ^ 2) = B - 2 * p * A + L * p ^ 2 := by
    calc
      _ = ∫ t in a..b, (g t ^ 2 - (2 * p) * g t) + p ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hB.sub (hA.const_mul _)) (continuous_const.intervalIntegrable _ _),
          intervalIntegral.integral_sub hB (hA.const_mul _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul]
  have hNN := intervalIntegral.integral_nonneg hab.le (f := fun t => (g t - p) ^ 2)
    (fun _ _ => sq_nonneg _)
  have hEq : B - 2 * p * A + L * p ^ 2 = B - A ^ 2 / L := by
    unfold p
    field_simp [hL.ne'] <;> ring
  rw [hId, hEq] at hNN
  exact ((div_le_iff₀ hL).mp (sub_nonneg.mp hNN)).trans_eq (mul_comm B L)

theorem interval_point_difference_sq_le {f f' : ℝ → ℂ}
    (hDeriv : ∀ t, HasDerivAt f (f' t) t) (hCont : Continuous f')
    {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖f' t‖ ^ 2 := by
  have hAll (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      ‖f v - f u‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖f' t‖ ^ 2 := by
    by_cases hEq : u = v
    · rw [hEq, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact mul_nonneg (sub_nonneg.mpr (hu.1.trans hu.2))
        (intervalIntegral.integral_nonneg (hu.1.trans hu.2) (fun _ _ => sq_nonneg _))
    have hFTC : (∫ t in u..v, f' t) = f v - f u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hDeriv t) (hCont.intervalIntegrable _ _)
    have hNorm : ‖f v - f u‖ ≤ ∫ t in u..v, ‖f' t‖ := by
      rw [← hFTC]
      exact intervalIntegral.norm_integral_le_integral_norm huv
    have hE : (∫ t in u..v, ‖f' t‖ ^ 2) ≤ ∫ t in a..b, ‖f' t‖ ^ 2 :=
      intervalIntegral.integral_mono_interval hu.1 huv hv.2
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ((hCont.norm.pow 2).intervalIntegrable _ _)
    calc
      _ ≤ (∫ t in u..v, ‖f' t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
      _ ≤ (v - u) * ∫ t in u..v, ‖f' t‖ ^ 2 :=
        interval_integral_sq_le (fun t => ‖f' t‖) hCont.norm (lt_of_le_of_ne huv hEq)
      _ ≤ (b - a) * ∫ t in a..b, ‖f' t‖ ^ 2 :=
        mul_le_mul (by linarith [hu.1, hv.2]) hE
          (intervalIntegral.integral_nonneg huv (fun _ _ => sq_nonneg _))
          (sub_nonneg.mpr (hu.1.trans hu.2))
  by_cases hxy : x ≤ y
  · rw [norm_sub_rev]
    exact hAll x y hx hy hxy
  · exact hAll y x hy hx (le_of_not_ge hxy)

def intervalCellMean (f : ℝ → ℂ) (a b : ℝ) : ℂ :=
  (((b - a)⁻¹ : ℝ) : ℂ) * ∫ t in a..b, f t

theorem norm_sq_intervalCellMean_le {f : ℝ → ℂ} (hF : Continuous f)
    {a b : ℝ} (hab : a < b) :
    ‖intervalCellMean f a b‖ ^ 2 ≤ (∫ t in a..b, ‖f t‖ ^ 2) / (b - a) := by
  let L := b - a
  let E := ∫ t in a..b, ‖f t‖ ^ 2
  have hL : 0 < L := sub_pos.mpr hab
  have hN : ‖∫ t in a..b, f t‖ ≤ ∫ t in a..b, ‖f t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab.le
  have hK : ‖∫ t in a..b, f t‖ ^ 2 ≤ L * E :=
    (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans (interval_integral_sq_le (fun t => ‖f t‖) hF.norm hab)
  unfold intervalCellMean
  change ‖((L⁻¹ : ℝ) : ℂ) * (∫ t in a..b, f t)‖ ^ 2 ≤ E / L
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hL.le), mul_pow]
  calc
    _ ≤ (L⁻¹) ^ 2 * (L * E) := mul_le_mul_of_nonneg_left hK (sq_nonneg _)
    _ = _ := by field_simp [hL.ne'] <;> ring

theorem interval_cell_mean_error_sq_le {f f' : ℝ → ℂ}
    (hDeriv : ∀ t, HasDerivAt f (f' t) t) (hCont : Continuous f')
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    ‖f x - intervalCellMean f a b‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖f' t‖ ^ 2 := by
  let L := b - a
  let E := ∫ t in a..b, ‖f' t‖ ^ 2
  let C := Real.sqrt (L * E)
  have hL : 0 < L := sub_pos.mpr hab
  have hE : 0 ≤ E := intervalIntegral.integral_nonneg hab.le (fun _ _ => sq_nonneg _)
  have hF : Continuous f := (show Differentiable ℝ f from fun t => (hDeriv t).differentiableAt).continuous
  have hDiff (t : ℝ) (ht : t ∈ Icc a b) : ‖f x - f t‖ ≤ C :=
    Real.le_sqrt_of_sq_le (interval_point_difference_sq_le hDeriv hCont hx ht)
  have hMean : f x - intervalCellMean f a b =
      ((L⁻¹ : ℝ) : ℂ) * ∫ t in a..b, (f x - f t) := by
    rw [intervalCellMean, intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hF.intervalIntegrable _ _), intervalIntegral.integral_const, Complex.real_smul]
    change f x - ((L⁻¹ : ℝ) : ℂ) * (∫ t in a..b, f t) =
      ((L⁻¹ : ℝ) : ℂ) * ((L : ℂ) * f x - (∫ t in a..b, f t))
    have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    simp only [Complex.ofReal_inv]
    field_simp [hLC] <;> ring
  have hInt : (∫ t in a..b, ‖f x - f t‖) ≤ L * C := by
    calc
      _ ≤ ∫ t in a..b, C := intervalIntegral.integral_mono_on hab.le
        ((continuous_const.sub hF).norm.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hDiff
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]
  have hNorm : ‖f x - intervalCellMean f a b‖ ≤ C := by
    rw [hMean, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hL.le)]
    calc
      _ ≤ L⁻¹ * (∫ t in a..b, ‖f x - f t‖) :=
        mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab.le) (by positivity)
      _ ≤ L⁻¹ * (L * C) := mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  calc
    _ ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
    _ = _ := Real.sq_sqrt (mul_nonneg hL.le hE)

theorem interval_cell_mean_l2_error_le {f f' : ℝ → ℂ}
    (hDeriv : ∀ t, HasDerivAt f (f' t) t) (hCont : Continuous f')
    {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, ‖f t - intervalCellMean f a b‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ t in a..b, ‖f' t‖ ^ 2 := by
  let E := ∫ t in a..b, ‖f' t‖ ^ 2
  have hF : Continuous f := (show Differentiable ℝ f from fun t => (hDeriv t).differentiableAt).continuous
  calc
    _ ≤ ∫ _ in a..b, (b - a) * E := intervalIntegral.integral_mono_on hab.le
      (((hF.sub continuous_const).norm.pow 2).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (fun _ ht => interval_cell_mean_error_sq_le hDeriv hCont hab ht)
    _ = _ := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      change (b - a) * ((b - a) * E) = (b - a) ^ 2 * E
      ring

end
end ManuscriptAudit.Paper8IntervalCellApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8IntervalCellApproximation.interval_cell_mean_l2_error_le
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
