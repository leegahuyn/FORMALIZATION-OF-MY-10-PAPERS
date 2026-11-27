import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8InsideComplexAnalytic

/-! Comparing the complex holomorphic inside series on the positive real axis. -/

namespace ManuscriptAudit.Paper8InsideComplexComparison

open Paper8InsideComplexAnalytic
open Paper8ExteriorNormalization (negPochhammer ramanujanTerm ramanujanF)

noncomputable section

theorem pochhammer_ofReal (q : ℝ) (n : ℕ) :
    pochhammer (q : ℂ) n = ((negPochhammer q n : ℝ) : ℂ) := by
  unfold pochhammer negPochhammer
  change _ = Complex.ofRealHom (∏ j ∈ Finset.range n, (1 + q ^ (j + 1)))
  rw [map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [map_add, map_one, map_pow] <;> rfl

private theorem printedTerm_ofReal (q : ℝ) (n : ℕ) :
    ((Paper8PrintedInsideSeries.printedTerm q n : ℝ) : ℂ) = printedTerm n (q : ℂ) := by
  rw [Paper8PrintedInsideSeries.printedTerm, printedTerm, pochhammer_ofReal,
    Complex.ofReal_div, Complex.ofReal_pow]

private theorem standardTerm_ofReal (q : ℝ) (n : ℕ) :
    ((ramanujanTerm q n : ℝ) : ℂ) = standardTerm n (q : ℂ) := by
  rw [ramanujanTerm, standardTerm, pochhammer_ofReal, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_pow]

theorem printed_ofReal {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    printed (q : ℂ) = (Paper8PrintedInsideSeries.printedInside q : ℂ) := by
  obtain ⟨hp, _⟩ := Paper8PrintedInsideSeries.printed_and_standard_summable hq h₁
  have h := Complex.ofRealCLM.hasSum hp.hasSum
  change HasSum (fun n => ((Paper8PrintedInsideSeries.printedTerm q n : ℝ) : ℂ))
    (Paper8PrintedInsideSeries.printedInside q : ℂ) at h
  simp only [printedTerm_ofReal] at h
  exact h.tsum_eq

theorem standard_ofReal {q : ℝ} (hq : 0 ≤ q) (h₁ : q < 1) :
    standard (q : ℂ) = (ramanujanF q : ℂ) := by
  obtain ⟨_, hs⟩ := Paper8PrintedInsideSeries.printed_and_standard_summable hq h₁
  have h := Complex.ofRealCLM.hasSum hs.hasSum
  change HasSum (fun n => ((ramanujanTerm q n : ℝ) : ℂ)) (ramanujanF q : ℂ) at h
  simp only [standardTerm_ofReal] at h
  exact h.tsum_eq

theorem complex_inside_realParts_strict {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    (standard (q : ℂ)).re < (printed (q : ℂ)).re := by
  rw [printed_ofReal hq.le h₁, standard_ofReal hq.le h₁, Complex.ofReal_re, Complex.ofReal_re]
  exact Paper8PrintedInsideSeries.printedInside_gt_ramanujanF hq h₁

theorem complex_inside_half_gap :
    (2 / 45 : ℝ) ≤ (printed (1 / 2 : ℂ) - standard (1 / 2 : ℂ)).re := by
  have h : ((↑((1 / 2 : ℝ))) : ℂ) = 1 / 2 := by norm_num
  rw [← h, Complex.sub_re, printed_ofReal (by norm_num) (by norm_num),
    standard_ofReal (by norm_num) (by norm_num), Complex.ofReal_re, Complex.ofReal_re]
  exact Paper8PrintedInsideSeries.half_argument_gap

end
end ManuscriptAudit.Paper8InsideComplexComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8InsideComplexComparison.pochhammer_ofReal,
      ``ManuscriptAudit.Paper8InsideComplexComparison.printed_ofReal,
      ``ManuscriptAudit.Paper8InsideComplexComparison.standard_ofReal,
      ``ManuscriptAudit.Paper8InsideComplexComparison.complex_inside_realParts_strict,
      ``ManuscriptAudit.Paper8InsideComplexComparison.complex_inside_half_gap] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
