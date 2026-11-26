import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.PrintedRademacherTail

/-!
# The literal Rademacher partial sums at n = 50

With the appendix's single polar datum (1, 1), the c = 2 contribution
strictly dominates the c = 3 through c = 22 terms combined. The result
uses only the unit norm of the multiplier and does not depend on how
its phases are evaluated numerically.
-/

namespace ManuscriptAudit.RademacherAppendixNonzero

open PrintedRademacherTail

noncomputable section

def unitNumerators (c : ℕ) : Finset ℕ :=
  (Finset.range c).filter fun h => h.Coprime c

private theorem unitNumerators_two : unitNumerators 2 = {1} := by decide

private theorem unitNumerators_card_le (c : ℕ) : (unitNumerators c).card ≤ c := by
  simpa [unitNumerators] using
    Finset.card_filter_le (s := Finset.range c) (fun h => Nat.Coprime h c)

def phase (n c h : ℕ) : ℂ :=
  Complex.exp ((2 * Real.pi * (((n : ℝ) * h - (((h : ZMod c)⁻¹).val : ℝ)) / c) : ℝ) *
    Complex.I)

theorem phase_norm (n c h : ℕ) : ‖phase n c h‖ = 1 := by
  rw [phase, Complex.norm_exp, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero]

def argumentScale : ℝ := 4 * Real.pi * Real.sqrt 50

def besselContribution (weight : ℕ → ℕ → ℂ) (c : ℕ) : ℂ :=
  (↑(printedBessel (argumentScale / c) / (c : ℝ)) : ℂ) *
    ∑ h ∈ unitNumerators c, weight c h * phase 50 c h

def appendixPartial (weight : ℕ → ℕ → ℂ) (K : ℕ) : ℂ :=
  (↑(2 * Real.pi) : ℂ) * ∑ k ∈ Finset.range K, besselContribution weight (k + 1)

variable (weight : ℕ → ℕ → ℂ)
variable (hWeight : ∀ c h, h ∈ unitNumerators c → ‖weight c h‖ = 1)

private theorem scale_gt : 84 < argumentScale := by
  have hS : (7 : ℝ) < Real.sqrt 50 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 50)
    nlinarith [Real.sqrt_nonneg 50]
  unfold argumentScale
  have h : (3 : ℝ) * 7 < Real.pi * Real.sqrt 50 :=
    (mul_lt_mul_of_pos_left hS (by norm_num : (0 : ℝ) < 3)).trans_le
      (mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.sqrt_nonneg _))
  linarith

private def commonBesselScale : ℝ := Real.sqrt (Real.pi / (2 * argumentScale))

private theorem commonBesselScale_pos : 0 < commonBesselScale := by
  unfold commonBesselScale
  exact Real.sqrt_pos.mpr (div_pos Real.pi_pos (by linarith [scale_gt]))

private theorem bessel_rescale (c : ℝ) (hc : 0 < c) :
    printedBessel (argumentScale / c) =
      (commonBesselScale * Real.sqrt c) * Real.sinh (argumentScale / c) := by
  unfold printedBessel commonBesselScale
  have hA : 0 < argumentScale := by linarith [scale_gt]
  rw [show Real.pi / (2 * (argumentScale / c)) =
    (Real.pi / (2 * argumentScale)) * c by field_simp]
  rw [Real.sqrt_mul (by positivity)]

private theorem bessel_over_pos_nonneg (c : ℝ) (hc : 0 < c) :
    0 ≤ printedBessel (argumentScale / c) / c := by
  have hA : 0 < argumentScale := by linarith [scale_gt]
  exact div_nonneg ((printedBessel_lower _ (div_pos hA hc)).trans'
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hc.le

include hWeight

private theorem norm_contribution_two :
    ‖besselContribution weight 2‖ = printedBessel (argumentScale / 2) / 2 := by
  unfold besselContribution
  rw [unitNumerators_two, Finset.sum_singleton, norm_mul, norm_mul,
    hWeight 2 1 (by simp [unitNumerators_two]), phase_norm, one_mul, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  simp only [Nat.cast_ofNat]
  exact abs_of_nonneg (bessel_over_pos_nonneg 2 (by norm_num))

private theorem norm_contribution_le_bessel {c : ℕ} (hc : 0 < c) :
    ‖besselContribution weight c‖ ≤ printedBessel (argumentScale / c) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hCard : ((unitNumerators c).card : ℝ) ≤ c := by
    exact_mod_cast unitNumerators_card_le c
  have hS : ‖∑ h ∈ unitNumerators c, weight c h * phase 50 c h‖ ≤ (c : ℝ) := by
    calc
      _ ≤ ∑ h ∈ unitNumerators c, ‖weight c h * phase 50 c h‖ := norm_sum_le _ _
      _ = ∑ _h ∈ unitNumerators c, (1 : ℝ) :=
        Finset.sum_congr rfl fun h hh => by rw [norm_mul, hWeight c h hh, phase_norm, one_mul]
      _ = ((unitNumerators c).card : ℝ) := by simp
      _ ≤ _ := hCard
  rw [besselContribution, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bessel_over_pos_nonneg c hc')]
  exact (mul_le_mul_of_nonneg_left hS (bessel_over_pos_nonneg c hc')).trans_eq
    (div_mul_cancel₀ _ hc'.ne')

omit hWeight in
private theorem sinh_scale_comparison :
    200 * Real.sinh (argumentScale / 3) < Real.sinh (argumentScale / 2) := by
  have h2 : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith only [h]
  have h9 : (2 : ℝ) ^ (9 : ℕ) < Real.exp 9 := by
    rw [show (9 : ℝ) = (9 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ h2 (by norm_num) (by decide)
  have h9le : (9 : ℝ) ≤ argumentScale / 6 := by linarith [scale_gt]
  have he : (201 : ℝ) < Real.exp (argumentScale / 6) := by
    have hmono := Real.exp_le_exp.mpr h9le
    norm_num at h9
    linarith
  have hProd : Real.exp (argumentScale / 3) * Real.exp (argumentScale / 6) =
      Real.exp (argumentScale / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hS := Real.exp_lt_exp.mpr
    (show -(argumentScale / 2) < argumentScale / 3 by linarith [scale_gt])
  let a := Real.exp (argumentScale / 3)
  let d := Real.exp (-(argumentScale / 2))
  let c := Real.exp (argumentScale / 6)
  have hMul : a * 201 < a * c := mul_lt_mul_of_pos_left he (Real.exp_pos _)
  have hDiff : 200 * a < a * c - d := calc
    200 * a = a * 201 - a := by ring
    _ ≤ a * 201 - d := sub_le_sub_left hS.le _
    _ < a * c - d := sub_lt_sub_right hMul _
  rw [Real.sinh_eq, Real.sinh_eq, ← hProd]
  change 200 * ((a - Real.exp (-(argumentScale / 3))) / 2) < (a * c - d) / 2
  calc
    _ ≤ (200 * a) / 2 := by
      have h := (Real.exp_pos (-(argumentScale / 3))).le
      linarith
    _ < _ := div_lt_div_of_pos_right hDiff (by norm_num)

private theorem norm_contribution_tail_le {c : ℕ} (hlo : 3 ≤ c) (hhi : c ≤ 22) :
    ‖besselContribution weight c‖ ≤
      5 * commonBesselScale * Real.sinh (argumentScale / 3) := by
  have hc : 0 < c := by omega
  have h₃ : (3 : ℝ) ≤ c := by exact_mod_cast hlo
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have h₂₂ : (c : ℝ) ≤ 22 := by exact_mod_cast hhi
  have hSqrt : Real.sqrt (c : ℝ) ≤ 5 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 5 by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hA : 0 < argumentScale := by linarith [scale_gt]
  have hC := commonBesselScale_pos
  calc
    _ ≤ printedBessel (argumentScale / c) := norm_contribution_le_bessel weight hWeight hc
    _ = (commonBesselScale * Real.sqrt (c : ℝ)) * Real.sinh (argumentScale / c) :=
      bessel_rescale _ hc'
    _ ≤ (commonBesselScale * 5) * Real.sinh (argumentScale / 3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hSqrt hC.le)
        (Real.sinh_strictMono.monotone (div_le_div_of_nonneg_left hA.le (by norm_num) h₃))
        (Real.sinh_pos_iff.mpr (div_pos hA hc')).le (by positivity)
    _ = _ := by ring

private theorem norm_contribution_two_gt_tail :
    ‖∑ j ∈ Finset.range 20, besselContribution weight (j + 3)‖ <
      ‖besselContribution weight 2‖ := by
  have hC := commonBesselScale_pos
  have h₂ : (1 : ℝ) ≤ Real.sqrt 2 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
  have hy : 0 < Real.sinh (argumentScale / 2) :=
    Real.sinh_pos_iff.mpr (by linarith [scale_gt])
  calc
    _ ≤ ∑ j ∈ Finset.range 20, ‖besselContribution weight (j + 3)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range 20, 5 * commonBesselScale * Real.sinh (argumentScale / 3) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact norm_contribution_tail_le weight hWeight (c := j + 3) (by omega) (by omega)
    _ = 100 * commonBesselScale * Real.sinh (argumentScale / 3) := by simp; ring
    _ < commonBesselScale * Real.sinh (argumentScale / 2) / 2 := by
      have h := mul_lt_mul_of_pos_left sinh_scale_comparison hC
      linarith only [h]
    _ ≤ (commonBesselScale * Real.sqrt 2) * Real.sinh (argumentScale / 2) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ hC.le) hy.le
    _ = ‖besselContribution weight 2‖ := by
      rw [norm_contribution_two weight hWeight, bessel_rescale _ (by norm_num)]

/-- The absolute difference from the first term in the printed n = 50 row is positive. -/
theorem appendix_n50_K22_first_term_difference_ne_zero :
    appendixPartial weight 22 - appendixPartial weight 1 ≠ 0 := by
  have hSplit : appendixPartial weight 22 - appendixPartial weight 1 =
      (↑(2 * Real.pi) : ℂ) * (besselContribution weight 2 +
        ∑ j ∈ Finset.range 20, besselContribution weight (j + 3)) := by
    unfold appendixPartial
    rw [show (22 : ℕ) = 2 + 20 by decide, Finset.sum_range_add, Finset.sum_range_succ _ 1]
    simp only [Finset.sum_range_one, Nat.zero_add, Nat.reduceAdd]
    have hIdx (j : ℕ) : 2 + j + 1 = j + 3 := by omega
    simp only [hIdx]
    ring
  rw [hSplit]
  intro hzero
  have hπ : (↑(2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  have he := (mul_eq_zero.mp hzero).resolve_left hπ
  have hNeg : besselContribution weight 2 =
      -(∑ j ∈ Finset.range 20, besselContribution weight (j + 3)) := by
    linear_combination he
  have hStrict := norm_contribution_two_gt_tail weight hWeight
  rw [hNeg, norm_neg] at hStrict
  exact (lt_irrefl _) hStrict

end
end ManuscriptAudit.RademacherAppendixNonzero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.RademacherAppendixNonzero.phase_norm,
      ``ManuscriptAudit.RademacherAppendixNonzero.appendix_n50_K22_first_term_difference_ne_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
