import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Pi.Bounds
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourMoment
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourCoefficientDecay

/-!
# Quantitative alternating moment in the reciprocal contour

The lower-half-plane exponents are −1 and −46/3. Their moment
difference is positive and lies between three quarters of its first
nonzero term and that first term.
-/

namespace ManuscriptAudit.Paper8ReciprocalContourMoment

open Paper8ContourGammaSeries (scale coefficient coefficient_pos coefficient_succ)
open Paper8ContourCoefficientDecay (coefficient_succ_le_decay)
open Paper8ContourSignedDominance (decay)
open Paper8ContourMoment (atZero hasSum_atZero_re)
open Paper8ContourMomentTerm (coefficientMoment)

noncomputable section

def magnitude (k n : ℕ) : ℝ :=
  coefficient k (n + 1) * ((46 / 3 : ℝ) ^ (n + 1) - 1) / (((n + 1).factorial : ℕ) : ℝ)

def momentDifference (k : ℕ) (r : ℝ) : ℝ :=
  (atZero (-1) k r).re - (atZero (-46 / 3) k r).re

private theorem magnitude_pos {k : ℕ} (hk : 0 < k) (n : ℕ) : 0 < magnitude k n := by
  unfold magnitude
  have hp : (1 : ℝ) < (46 / 3 : ℝ) ^ (n + 1) :=
    one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  exact div_pos (mul_pos (coefficient_pos hk _) (sub_pos.mpr hp)) (by positivity)

private theorem scale_nonneg_le {k : ℕ} (hk : 0 < k) : 0 ≤ scale k ∧ scale k ≤ 4 / 15 := by
  have hCast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from hk)
  unfold scale
  have hDen : (0 : ℝ) < 12 * (k : ℝ) := by positivity
  refine ⟨div_nonneg Real.pi_pos.le hDen.le, (div_le_iff₀ hDen).2 ?_⟩
  linarith [Real.pi_lt_d2]

private theorem magnitude_succ_le {k : ℕ} (hk : 0 < k) (n : ℕ) :
    magnitude k (n + 1) ≤ (1 / 4) * magnitude k n := by
  let m := n + 1
  let x : ℝ := 46 / 3
  have hm : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hPow : x ≤ x ^ m := by
    unfold m
    rw [pow_succ']
    have hX : 1 ≤ x := by norm_num [x]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hX) (by positivity : 0 ≤ x)
  have hExp : x ^ (m + 1) - 1 ≤ (x + 1) * (x ^ m - 1) := by
    rw [pow_succ]
    nlinarith only [hPow]
  have hDen : (5 : ℝ) ≤ ((m : ℝ) + 3 / 2) * ((m : ℝ) + 1) := by
    have h₁ : (5 / 2 : ℝ) ≤ (m : ℝ) + 3 / 2 := by linarith
    have h₂ : (2 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    calc
      _ = (5 / 2 : ℝ) * 2 := by norm_num
      _ ≤ _ := mul_le_mul h₁ h₂ (by norm_num) (by positivity)
  have hDenPos : (0 : ℝ) < ((m : ℝ) + 3 / 2) * ((m : ℝ) + 1) :=
    (by norm_num : (0 : ℝ) < 5).trans_le hDen
  have hScale := scale_nonneg_le hk
  have hConst : scale k ^ 2 / (((m : ℝ) + 3 / 2) * ((m : ℝ) + 1)) * (x + 1) ≤ 1 / 4 := by
    have hs : scale k ^ 2 ≤ (4 / 15 : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ hScale.1 hScale.2 2
    rw [div_mul_eq_mul_div, div_le_iff₀ hDenPos]
    change scale k ^ 2 * (46 / 3 + 1) ≤
      1 / 4 * (((m : ℝ) + 3 / 2) * ((m : ℝ) + 1))
    nlinarith only [hs, hDen]
  have hFac : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hMul : 0 ≤ coefficient k m / (m.factorial : ℝ) := by
    exact div_nonneg (coefficient_pos hk m).le hFac.le
  change coefficient k (m + 1) * (x ^ (m + 1) - 1) / ((m + 1).factorial : ℝ) ≤
    1 / 4 * (coefficient k m * (x ^ m - 1) / (m.factorial : ℝ))
  calc
    _ = (scale k ^ 2 / (((m : ℝ) + 3 / 2) * ((m : ℝ) + 1))) *
        (coefficient k m / (m.factorial : ℝ) * (x ^ (m + 1) - 1)) := by
      rw [coefficient_succ hk, Nat.factorial_succ]
      push_cast
      have h₁ : (m : ℝ) + 3 / 2 ≠ 0 := by positivity
      have h₂ : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp [h₁, h₂, hFac.ne'] <;> ring
    _ ≤ (scale k ^ 2 / (((m : ℝ) + 3 / 2) * ((m : ℝ) + 1))) *
        (coefficient k m / (m.factorial : ℝ) * ((x + 1) * (x ^ m - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hExp hMul) (by positivity)
    _ = (scale k ^ 2 / (((m : ℝ) + 3 / 2) * ((m : ℝ) + 1)) * (x + 1)) *
        (coefficient k m * (x ^ m - 1) / (m.factorial : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hConst (by
      have hp : 0 ≤ x ^ m - 1 := by
        have hx : 1 ≤ x := by norm_num [x]
        exact sub_nonneg.mpr (hx.trans hPow)
      exact div_nonneg (mul_nonneg (coefficient_pos hk m).le hp) hFac.le)

theorem momentDifference_hasSum {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * magnitude k n) (momentDifference k r) := by
  let f : ℕ → ℝ := fun n => coefficientMoment (-1) k n - coefficientMoment (-46 / 3) k n
  have hRaw : HasSum f (momentDifference k r) :=
    (hasSum_atZero_re hk (-1) hr).sub (hasSum_atZero_re hk (-46 / 3) hr)
  have hZero : f 0 = 0 := by simp [f, coefficientMoment]
  have hTail : HasSum (fun n : ℕ => f (n + 1)) (momentDifference k r) := by
    have h := (hasSum_nat_add_iff' 1).2 hRaw
    simpa only [Finset.sum_range_one, hZero, sub_zero] using h
  refine hTail.congr fun n => ?_
  have hNeg : (-46 / 3 : ℝ) = (-1 : ℝ) * (46 / 3) := by norm_num
  have ht : (-46 / 3 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n + 1) * (46 / 3 : ℝ) ^ (n + 1) := by
    rw [← mul_pow, ← hNeg]
  change coefficientMoment (-1) k (n + 1) - coefficientMoment (-46 / 3) k (n + 1) = _
  unfold coefficientMoment magnitude
  rw [ht, pow_succ (-1 : ℝ) n]
  ring

theorem momentDifference_bounds {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    3 / 4 * magnitude k 0 ≤ momentDifference k r ∧ momentDifference k r ≤ magnitude k 0 := by
  have hLimit := (momentDifference_hasSum hk hr).tendsto_sum_nat
  have hAnt : Antitone (magnitude k) := by
    apply antitone_nat_of_succ_le
    intro n
    have h := magnitude_succ_le hk n
    linarith [magnitude_pos hk n]
  have hl := hAnt.alternating_series_le_tendsto hLimit 1
  have hh := hAnt.tendsto_le_alternating_series hLimit 0
  norm_num [Finset.sum_range_succ] at hl hh
  exact ⟨by linarith [magnitude_succ_le hk 0], hh⟩

theorem magnitude_first_le_decay {k : ℕ} (hk : 0 < k) :
    magnitude k 0 ≤ decay k * magnitude 1 0 := by
  have h := coefficient_succ_le_decay hk 0
  norm_num [magnitude, Nat.factorial] at h ⊢
  linarith only [h]

end
end ManuscriptAudit.Paper8ReciprocalContourMoment

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReciprocalContourMoment.momentDifference_hasSum,
      ``ManuscriptAudit.Paper8ReciprocalContourMoment.momentDifference_bounds,
      ``ManuscriptAudit.Paper8ReciprocalContourMoment.magnitude_first_le_decay] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
