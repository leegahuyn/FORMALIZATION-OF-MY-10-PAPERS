import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper8EulerianExterior
import PrimalitySheafVerification.ManuscriptAudit.Paper8InsideComplexComparison

/-! The actual reciprocal Eulerian series is twice the recurrence sum at parameter one. -/

namespace ManuscriptAudit.Paper8EulerianRecurrenceBridge

open Paper8EulerianRecurrenceTerms Paper8EulerianRecurrence Paper8EulerianExterior
open Paper8ExteriorNormalization (negPochhammer)
open Paper8InsideComplexComparison (pochhammer_ofReal)

noncomputable section

private def starTail (q : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * q ^ triangular n / product q 1 (n + 1)

private theorem adjacent_star_tail {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    term q 1 n + term q 1 (n + 1) = starTail q n := by
  have hFormula : term q 1 n / (1 + q ^ (n + 1)) = starTail q n := by
    simp only [term, starTail, product_succ, one_pow, mul_one, one_mul, div_div_eq_div_mul]
  rw [← hFormula]
  apply (eq_div_iff (by positivity : 1 + q ^ (n + 1) ≠ 0)).mpr
  have h := adjacent_term hq (show (0 : ℝ) ≤ 1 by norm_num) n
  simp only [one_mul, one_pow, neg_one_mul] at h
  linear_combination h

private theorem starTail_cast (q : ℝ) (n : ℕ) :
    ((starTail q n : ℝ) : ℂ) = reciprocalStarTerm n (q : ℂ) := by
  have hProd : product q 1 (n + 1) = negPochhammer q (n + 1) := by
    simp only [product, negPochhammer, one_mul]
  rw [starTail, hProd, triangular_formula, reciprocalStarTerm, pochhammer_ofReal]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one]

theorem reciprocalStar_ofReal_eq_two_H {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    reciprocalStar (q : ℂ) = 2 * (H q 1 : ℂ) := by
  have hs := term_summable hq h₁ (show (0 : ℝ) ≤ 1 by norm_num) le_rfl
  have ht : Summable (fun n : ℕ => term q 1 (n + 1)) := (summable_nat_add_iff 1).mpr hs
  have hT : (∑' n : ℕ, term q 1 (n + 1)) = H q 1 - 1 := by
    have he := hs.tsum_eq_zero_add
    rw [term_zero] at he
    unfold H
    linarith only [he]
  have hSummable : Summable (starTail q) := (hs.add ht).congr (adjacent_star_tail hq)
  have hEq : (∑' n : ℕ, starTail q n) = H q 1 + (H q 1 - 1) := by
    simp_rw [← adjacent_star_tail hq]
    rw [hs.tsum_add ht, hT] <;> rfl
  have hReal : HasSum (starTail q) (H q 1 + (H q 1 - 1)) := by
    rw [← hEq]
    exact hSummable.hasSum
  have hComplex := Complex.ofRealCLM.hasSum hReal
  change HasSum (fun n => ((starTail q n : ℝ) : ℂ)) ((H q 1 + (H q 1 - 1) : ℝ) : ℂ) at hComplex
  simp only [starTail_cast] at hComplex
  rw [reciprocalStar, hComplex.tsum_eq, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]
  ring

end
end ManuscriptAudit.Paper8EulerianRecurrenceBridge

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8EulerianRecurrenceBridge.reciprocalStar_ofReal_eq_two_H
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
