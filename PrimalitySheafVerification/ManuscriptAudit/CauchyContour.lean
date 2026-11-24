import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Exact contour coefficients for finite Laurent sums

Paper 8, physical PDF p. 350, uses a circle integral to extract Laurent
coefficients. On a circle of positive radius centered at zero, this formula
recovers the actual target coefficient of each finite Laurent sum.
-/

open scoped BigOperators

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

end ManuscriptAudit.CauchyContour

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CauchyContour.finiteLaurent_contour_eq
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
