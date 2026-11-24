import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Exact contour coefficients for finite Laurent sums

Paper 8, physical PDF p. 350, uses a circle integral to extract Laurent
coefficients. On a circle of positive radius centered at zero, this formula
recovers the actual target coefficient of each finite Laurent sum.
-/

open Filter
open scoped BigOperators Topology

namespace ManuscriptAudit.CauchyContour

private theorem centered_zpow_integral {R : ℝ} (hR : 0 < R) (d : ℤ) :
    (∮ z in C(0, R), z ^ d) =
      if d = -1 then (2 : ℂ) * (Real.pi : ℂ) * Complex.I else 0 := by
  by_cases hd : d = -1
  · rw [if_pos hd, hd]
    simpa only [sub_zero, zpow_neg_one] using
      circleIntegral.integral_sub_center_inv (0 : ℂ) hR.ne'
  · rw [if_neg hd]
    simpa only [sub_zero] using circleIntegral.integral_sub_zpow_of_ne hd 0 0 R

/-- The normalized contour formula returns the exact Laurent coefficient. -/
theorem finiteLaurent_contour_eq (s : Finset ℤ) (a : ℤ → ℂ) {R : ℝ} (hR : 0 < R)
    (n : ℤ) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C(0, R), (∑ k ∈ s, a k * z ^ k) / z ^ (n + 1)) =
      if n ∈ s then a n else 0 := by
  let c : ℂ := (2 : ℂ) * (Real.pi : ℂ) * Complex.I
  have hCenter : (0 : ℂ) ∉ Metric.sphere (0 : ℂ) R := by
    intro hz
    have he : (0 : ℝ) = R := by simpa only [Metric.mem_sphere, dist_self] using hz
    exact hR.ne he
  have hExpand :
      (∮ z in C(0, R), (∑ k ∈ s, a k * z ^ k) / z ^ (n + 1)) =
        ∮ z in C(0, R), ∑ k ∈ s, a k * z ^ (k - (n + 1)) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hz0 : z ≠ 0 := fun he => hCenter (he ▸ hz)
    change (∑ k ∈ s, a k * z ^ k) / z ^ (n + 1) =
      ∑ k ∈ s, a k * z ^ (k - (n + 1))
    rw [div_eq_mul_inv, ← zpow_neg, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← zpow_add₀ hz0, ← sub_eq_add_neg]
  have hIntegrable (k : ℤ) (_ : k ∈ s) :
      CircleIntegrable (fun z : ℂ => a k * z ^ (k - (n + 1))) 0 R := by
    have hCenterAbs : (0 : ℂ) ∉ Metric.sphere (0 : ℂ) |R| := by
      simpa only [abs_of_pos hR] using hCenter
    have hp :
        CircleIntegrable (fun z : ℂ => (z - 0) ^ (k - (n + 1))) 0 R :=
      circleIntegrable_sub_zpow_iff.mpr (Or.inr (Or.inr hCenterAbs))
    simpa only [sub_zero, smul_eq_mul] using hp.const_fun_smul (a := a k)
  have hMonomial (k : ℤ) :
      (∮ z in C(0, R), a k * z ^ (k - (n + 1))) =
        if k = n then c * a n else 0 := by
    rw [circleIntegral.integral_const_mul, centered_zpow_integral hR]
    by_cases hk : k = n
    · subst k
      have hd : n - (n + 1) = -1 := by omega
      rw [if_pos hd, if_pos rfl]
      exact mul_comm _ _
    · have hd : k - (n + 1) ≠ -1 := by omega
      simp only [if_neg hd, if_neg hk, mul_zero]
  have hCoeff : (∮ z in C(0, R), (∑ k ∈ s, a k * z ^ k) / z ^ (n + 1)) =
      if n ∈ s then c * a n else 0 := by
    rw [hExpand, circleIntegral.integral_fun_sum hIntegrable]
    simp_rw [hMonomial]
    by_cases hn : n ∈ s
    · rw [if_pos hn, Finset.sum_eq_single_of_mem n hn]
      · rw [if_pos rfl]
      · intro k _ hk
        rw [if_neg hk]
    · rw [if_neg hn, Finset.sum_eq_zero]
      intro k hk
      have hkn : k ≠ n := fun he => hn (he ▸ hk)
      rw [if_neg hkn]
  have hc : c ≠ 0 := mul_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  change c⁻¹ * (∮ z in C(0, R), (∑ k ∈ s, a k * z ^ k) / z ^ (n + 1)) =
    if n ∈ s then a n else 0
  rw [hCoeff]
  by_cases hn : n ∈ s
  · simp only [if_pos hn, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · simp only [if_neg hn, mul_zero]

/-- Absolute convergence on the circle makes the normalized contour integral
recover the coefficient of the full Laurent series. -/
theorem absoluteLaurent_contour_eq (a : ℤ → ℂ) {R : ℝ} (hR : 0 < R)
    (n : ℤ) (hAbs : Summable (fun k : ℤ => ‖a k * (R : ℂ) ^ k‖)) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C(0, R), (∑' k : ℤ, a k * z ^ k) / z ^ (n + 1)) = a n := by
  let f (k : ℤ) (z : ℂ) : ℂ := a k * z ^ k / z ^ (n + 1)
  let b (k : ℤ) : ℝ := ‖a k * (R : ℂ) ^ k‖ / ‖(R : ℂ) ^ (n + 1)‖
  let c : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  letI : (Filter.atTop : Filter (Finset ℤ)).IsCountablyGenerated :=
    (Filter.atTop_basis (α := Finset ℤ)).isCountablyGenerated
  have hb : Summable b := by
    simpa only [b, div_eq_mul_inv] using hAbs.mul_right (‖(R : ℂ) ^ (n + 1)‖)⁻¹
  have hNorm (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) R) : ‖z‖ = R := by
    simpa only [dist_zero_right] using Metric.mem_sphere.mp hz
  have hBound (k : ℤ) (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) R) :
      ‖f k z‖ ≤ b k := by
    dsimp only [f, b]
    simp only [norm_div, norm_mul, norm_zpow, hNorm z hz, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR, le_rfl]
  have hContinuous (s : Finset ℤ) :
      ContinuousOn (fun z : ℂ => ∑ k ∈ s, f k z) (Metric.sphere (0 : ℂ) R) := by
    refine continuousOn_finsetSum _ fun k _ z hz => ?_
    have hz0 : z ≠ 0 := by
      intro he
      exact hR.ne (by simpa only [he, norm_zero] using hNorm z hz)
    exact ((continuousAt_const.mul (continuousAt_zpow₀ z k (Or.inl hz0))).div
      (continuousAt_zpow₀ z (n + 1) (Or.inl hz0)) (zpow_ne_zero _ hz0)).continuousWithinAt
  have hUniform := tendstoUniformlyOn_tsum hb hBound
  have hIntegral := hUniform.tendsto_circleIntegral_of_continuousOn hR.le
    (Filter.Eventually.of_forall hContinuous)
  have hNormalized : Filter.Tendsto
      (fun s : Finset ℤ => c * (∮ z in C(0, R), ∑ k ∈ s, f k z)) Filter.atTop
      (𝓝 (c * (∮ z in C(0, R), ∑' k : ℤ, f k z))) :=
    tendsto_const_nhds.mul hIntegral
  have hEventually : (fun _ : Finset ℤ => a n) =ᶠ[Filter.atTop]
      (fun s : Finset ℤ => c * (∮ z in C(0, R), ∑ k ∈ s, f k z)) := by
    filter_upwards [Filter.eventually_ge_atTop ({n} : Finset ℤ)] with s hs
    have hns : n ∈ s := hs (Finset.mem_singleton_self n)
    have hSum : (∮ z in C(0, R), ∑ k ∈ s, f k z) =
        ∮ z in C(0, R), (∑ k ∈ s, a k * z ^ k) / z ^ (n + 1) :=
      circleIntegral.integral_congr hR.le (fun z _ => (Finset.sum_div s
        (fun k => a k * z ^ k) (z ^ (n + 1))).symm)
    rw [hSum]
    symm
    simpa only [if_pos hns] using finiteLaurent_contour_eq s a hR n
  have hFinal : c * (∮ z in C(0, R), ∑' k : ℤ, f k z) = a n :=
    tendsto_nhds_unique hNormalized (tendsto_const_nhds.congr' hEventually)
  have hSeries : (∮ z in C(0, R), ∑' k : ℤ, f k z) =
      ∮ z in C(0, R), (∑' k : ℤ, a k * z ^ k) / z ^ (n + 1) :=
    circleIntegral.integral_congr hR.le (fun _ _ => tsum_div_const)
  rw [hSeries] at hFinal
  exact hFinal

end ManuscriptAudit.CauchyContour

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.CauchyContour.finiteLaurent_contour_eq,
    ``ManuscriptAudit.CauchyContour.absoluteLaurent_contour_eq] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
