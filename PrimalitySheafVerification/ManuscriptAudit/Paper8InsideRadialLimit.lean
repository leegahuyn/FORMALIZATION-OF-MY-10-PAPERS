import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Group.FunctionSeries
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrintedInsideSeries

/-! Both genuine real inside sums have the same radial limit at q = 1. -/

namespace ManuscriptAudit.Paper8InsideRadialLimit

open Filter Set
open Paper8ExteriorNormalization (negPochhammer one_le_negPochhammer ramanujanTerm ramanujanF)
open Paper8PrintedInsideSeries (printedTerm printedInside doubled_pochhammer_le_squared)
open scoped Topology

noncomputable section

private def exponentSum (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (j + 1)

private theorem exponentSum_double (n : ℕ) : 2 * exponentSum n = n * (n + 1) := by
  induction n with
  | zero => simp [exponentSum]
  | succ n ih =>
    rw [exponentSum, Finset.sum_range_succ, ← exponentSum]
    nlinarith only [ih]

private theorem exponentSum_even (n : ℕ) : exponentSum (2 * n) = 2 * n ^ 2 + n := by
  have h := exponentSum_double (2 * n)
  nlinarith only [h]

private theorem pochhammer_square_lower {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    4 ^ n * q ^ exponentSum n ≤ (negPochhammer q n) ^ 2 := by
  induction n with
  | zero => simp [exponentSum, negPochhammer]
  | succ n ih =>
    have hx : 4 * q ^ (n + 1) ≤ (1 + q ^ (n + 1)) ^ 2 := by
      nlinarith only [sq_nonneg (q ^ (n + 1) - 1)]
    calc
      _ = (4 ^ n * q ^ exponentSum n) * (4 * q ^ (n + 1)) := by
        rw [exponentSum, Finset.sum_range_succ, ← exponentSum, pow_add, pow_succ (4 : ℝ)]
        ring
      _ ≤ (negPochhammer q n) ^ 2 * (1 + q ^ (n + 1)) ^ 2 :=
        mul_le_mul ih hx (by positivity) (sq_nonneg _)
      _ = _ := by
        rw [← mul_pow]
        exact congrArg (fun x : ℝ => x ^ (2 : ℕ))
          (Finset.prod_range_succ (fun j : ℕ => 1 + q ^ (j + 1)) n).symm

theorem printedTerm_le_geom {q : ℝ} (hq : 1 / 4 ≤ q) (n : ℕ) :
    printedTerm q n ≤ (1 / 2 : ℝ) ^ n := by
  have hq₀ : 0 ≤ q := by linarith
  have hd : 0 < negPochhammer q (2 * n) := zero_lt_one.trans_le (one_le_negPochhammer hq₀ _)
  have hg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  have hSquared : printedTerm q n ^ 2 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 := by
    rw [printedTerm, div_pow]
    apply (div_le_iff₀ (pow_pos hd 2)).mpr
    have hPow : 1 ≤ (4 * q) ^ n := by
      simpa only [one_pow] using
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 ≤ 4 * q) n
    have hCoeff : ((1 / 2 : ℝ) ^ n) ^ 2 * ((4 : ℝ) ^ 2) ^ n = (4 : ℝ) ^ n := by
      rw [← pow_mul (1 / 2 : ℝ), Nat.mul_comm n 2, pow_mul, ← mul_pow]
      norm_num
    calc
      _ = q ^ (2 * n ^ 2) := by rw [← pow_mul, Nat.mul_comm (n ^ 2) 2]
      _ ≤ (4 * q) ^ n * q ^ (2 * n ^ 2) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hPow (pow_nonneg hq₀ _)
      _ = ((1 / 2 : ℝ) ^ n) ^ 2 * (4 ^ (2 * n) * q ^ exponentSum (2 * n)) := by
        rw [mul_pow, exponentSum_even, pow_add q, pow_mul (4 : ℝ) 2 n]
        calc
          _ = (4 : ℝ) ^ n * (q ^ (2 * n ^ 2) * q ^ n) := by ring
          _ = _ := by rw [← hCoeff]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pochhammer_square_lower hq₀ _) (sq_nonneg _)
  by_contra! hn
  have hPos := mul_pos (sub_pos.mpr hn) (add_pos_of_pos_of_nonneg (hg.trans_lt hn) hg)
  nlinarith only [hSquared, hPos]

private theorem pochhammer_continuous (n : ℕ) : Continuous fun q : ℝ => negPochhammer q n := by
  induction n with
  | zero => simpa only [negPochhammer, Finset.range_zero, Finset.prod_empty] using
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  | succ n ih =>
    have hFactor : Continuous (fun q : ℝ => 1 + q ^ (n + 1)) :=
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).add
        ((continuous_id : Continuous (id : ℝ → ℝ)).pow (n + 1))
    have h := ih.mul hFactor
    rw [show (fun q : ℝ => negPochhammer q (n + 1)) =
        (fun q : ℝ => negPochhammer q n) * (fun q : ℝ => 1 + q ^ (n + 1)) by
          funext q
          exact Finset.prod_range_succ (fun j : ℕ => 1 + q ^ (j + 1)) n]
    exact h

theorem printedInside_continuousOn_radial :
    ContinuousOn printedInside (Icc (1 / 4 : ℝ) 1) := by
  unfold printedInside
  refine continuousOn_tsum (f := fun n q => printedTerm q n) (fun n => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) ?_
  · intro q hq
    have hq₀ : 0 ≤ q := by linarith [hq.1]
    exact (((continuous_id.pow (n ^ 2)).continuousAt).div ((pochhammer_continuous (2 * n)).continuousAt)
      (ne_of_gt (zero_lt_one.trans_le (one_le_negPochhammer hq₀ _)))).continuousWithinAt
  · intro n q hq
    have hq₀ : 0 ≤ q := by linarith [hq.1]
    have hnonneg : 0 ≤ printedTerm q n :=
      div_nonneg (pow_nonneg hq₀ _) (zero_le_one.trans (one_le_negPochhammer hq₀ _))
    rw [Real.norm_of_nonneg hnonneg]
    exact printedTerm_le_geom hq.1 n

theorem ramanujanF_continuousOn_radial :
    ContinuousOn ramanujanF (Icc (1 / 4 : ℝ) 1) := by
  unfold ramanujanF
  refine continuousOn_tsum (f := fun n q => ramanujanTerm q n) (fun n => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) ?_
  · intro q hq
    have hq₀ : 0 ≤ q := by linarith [hq.1]
    exact (((continuous_id.pow (n ^ 2)).continuousAt).div
      (((pochhammer_continuous n).pow 2).continuousAt)
      (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans_le (one_le_negPochhammer hq₀ _))))).continuousWithinAt
  · intro n q hq
    have hq₀ : 0 ≤ q := by linarith [hq.1]
    have hnonneg : 0 ≤ ramanujanTerm q n := div_nonneg (pow_nonneg hq₀ _) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnonneg]
    have hden : 0 < negPochhammer q (2 * n) :=
      zero_lt_one.trans_le (one_le_negPochhammer hq₀ _)
    exact (div_le_div_of_nonneg_left (pow_nonneg hq₀ _) hden
      (doubled_pochhammer_le_squared hq₀ hq.2 n)).trans (printedTerm_le_geom hq.1 n)

private theorem pochhammer_one (n : ℕ) : negPochhammer 1 n = (2 : ℝ) ^ n := by
  norm_num [negPochhammer]

private theorem geometric_sum : (∑' n : ℕ, (1 / 4 : ℝ) ^ n) = 4 / 3 := by
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)]
  norm_num

theorem inside_values_at_one : printedInside 1 = 4 / 3 ∧ ramanujanF 1 = 4 / 3 := by
  have hG (n : ℕ) : 1 / ((2 : ℝ) ^ 2) ^ n = (1 / 4 : ℝ) ^ n := by
    rw [one_div, ← inv_pow]
    norm_num
  have hP : (fun n => printedTerm 1 n) = fun n => (1 / 4 : ℝ) ^ n := by
    funext n
    simpa only [printedTerm, one_pow, pochhammer_one, pow_mul (2 : ℝ) 2 n] using hG n
  have hS : (fun n => ramanujanTerm 1 n) = fun n => (1 / 4 : ℝ) ^ n := by
    funext n
    simpa only [ramanujanTerm, one_pow, pochhammer_one, ← pow_mul, Nat.mul_comm n 2] using hG n
  rw [printedInside, ramanujanF, hP, hS, geometric_sum]
  exact ⟨rfl, rfl⟩

theorem inside_radial_limits :
    Tendsto printedInside (𝓝[ Icc (1 / 4 : ℝ) 1 ] 1) (𝓝 (4 / 3)) ∧
    Tendsto ramanujanF (𝓝[ Icc (1 / 4 : ℝ) 1 ] 1) (𝓝 (4 / 3)) := by
  have h : (1 : ℝ) ∈ Icc (1 / 4 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  exact ⟨inside_values_at_one.1 ▸ printedInside_continuousOn_radial 1 h,
    inside_values_at_one.2 ▸ ramanujanF_continuousOn_radial 1 h⟩

end
end ManuscriptAudit.Paper8InsideRadialLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8InsideRadialLimit.printedTerm_le_geom,
      ``ManuscriptAudit.Paper8InsideRadialLimit.printedInside_continuousOn_radial,
      ``ManuscriptAudit.Paper8InsideRadialLimit.ramanujanF_continuousOn_radial,
      ``ManuscriptAudit.Paper8InsideRadialLimit.inside_values_at_one,
      ``ManuscriptAudit.Paper8InsideRadialLimit.inside_radial_limits] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
