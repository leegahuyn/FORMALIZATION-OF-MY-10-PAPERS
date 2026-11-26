import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorNormalization

/-!
# The printed inside series and Ramanujan's f

Physical pp. 341, 355–356 of the manuscript put the index 2n in the
q-Pochhammer symbol. The standard f instead squares the n-factor
product, as in Bridges–Bringmann, equation (1.4):
https://www.mi.uni-koeln.de/Bringmann/Rademacherwithoutsequences.pdf#page=2

The two actual convergent sums differ throughout the positive unit interval.
-/

namespace ManuscriptAudit.Paper8PrintedInsideSeries

open Paper8ExteriorNormalization (negPochhammer one_le_negPochhammer ramanujanTerm ramanujanF)

noncomputable section

def printedTerm (q : ℝ) (n : ℕ) : ℝ :=
  q ^ (n ^ 2) / negPochhammer q (2 * n)

def printedInside (q : ℝ) : ℝ := ∑' n : ℕ, printedTerm q n

theorem doubled_pochhammer_le_squared {q : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (n : ℕ) :
    negPochhammer q (2 * n) ≤ (negPochhammer q n) ^ 2 := by
  unfold negPochhammer
  rw [two_mul, Finset.prod_range_add, pow_two]
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (one_le_negPochhammer hq n))
  apply Finset.prod_le_prod
  · intro j _
    exact zero_le_one.trans (le_add_of_nonneg_right (pow_nonneg hq _))
  · intro j _
    exact add_le_add_left (pow_le_pow_right_of_le_one hq h₁ (by omega)) 1

private theorem summable_of_pochhammer_bound {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1)
    (denom : ℕ → ℝ) (hD : ∀ n, 1 ≤ denom n) :
    Summable (fun n : ℕ => q ^ (n ^ 2) / denom n) := by
  have hGeom : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq h₁
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (pow_nonneg hq _) (zero_le_one.trans (hD n)))
    _ hGeom
  intro n
  calc
    _ ≤ q ^ (n ^ 2) / 1 :=
      div_le_div_of_nonneg_left (pow_nonneg hq _) zero_lt_one (hD n)
    _ = q ^ (n ^ 2) := div_one _
    _ ≤ _ := by
      have hn : n ≤ n ^ 2 := by
        cases n with
        | zero => decide
        | succ n => nlinarith
      exact pow_le_pow_right_of_le_one hq h₁.le hn

theorem printed_and_standard_summable {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    Summable (printedTerm q) ∧ Summable (ramanujanTerm q) :=
  ⟨summable_of_pochhammer_bound hq h₁ _ fun n => one_le_negPochhammer hq _,
    summable_of_pochhammer_bound hq h₁ _ fun n => by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (one_le_negPochhammer hq n) 2⟩

private theorem ramanujanTerm_le_printedTerm {q : ℝ} (hq : 0 ≤ q) (h₁ : q ≤ 1) (n : ℕ) :
    ramanujanTerm q n ≤ printedTerm q n :=
  div_le_div_of_nonneg_left (pow_nonneg hq _)
    (zero_lt_one.trans_le (one_le_negPochhammer hq _))
    (doubled_pochhammer_le_squared hq h₁ _)

private theorem first_term_strict {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    ramanujanTerm q 1 < printedTerm q 1 := by
  have hq2 : q ^ (2 : ℕ) < q := by nlinarith [mul_pos hq (sub_pos.mpr h₁)]
  have hd : (1 + q) * (1 + q ^ (2 : ℕ)) < (1 + q) ^ 2 := by
    rw [pow_two]
    exact mul_lt_mul_of_pos_left (add_lt_add_left hq2 _) (by positivity)
  have hpos : 0 < (1 + q) * (1 + q ^ (2 : ℕ)) := by positivity
  have hDivide := div_lt_div_of_pos_left hq hpos hd
  simpa [ramanujanTerm, printedTerm, negPochhammer, Finset.prod_range_succ] using hDivide

theorem gap_ge_first_term {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    printedTerm q 1 - ramanujanTerm q 1 ≤ printedInside q - ramanujanF q := by
  obtain ⟨hp, hs⟩ := printed_and_standard_summable hq h₁
  unfold printedInside ramanujanF
  rw [← hp.tsum_sub hs]
  exact (hp.sub hs).le_tsum 1 (fun n _ =>
    sub_nonneg.mpr (ramanujanTerm_le_printedTerm hq h₁.le n))

theorem printedInside_gt_ramanujanF {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    ramanujanF q < printedInside q :=
  sub_pos.mp ((sub_pos.mpr (first_term_strict hq h₁)).trans_le (gap_ge_first_term hq.le h₁))

theorem half_argument_gap :
    (2 / 45 : ℝ) ≤ printedInside (1 / 2) - ramanujanF (1 / 2) := by
  refine le_trans ?_ (gap_ge_first_term (q := 1 / 2) (by norm_num) (by norm_num))
  norm_num [printedTerm, ramanujanTerm, negPochhammer, Finset.prod_range_succ]

end
end ManuscriptAudit.Paper8PrintedInsideSeries

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8PrintedInsideSeries.doubled_pochhammer_le_squared,
      ``ManuscriptAudit.Paper8PrintedInsideSeries.printed_and_standard_summable,
      ``ManuscriptAudit.Paper8PrintedInsideSeries.gap_ge_first_term,
      ``ManuscriptAudit.Paper8PrintedInsideSeries.printedInside_gt_ramanujanF,
      ``ManuscriptAudit.Paper8PrintedInsideSeries.half_argument_gap] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
