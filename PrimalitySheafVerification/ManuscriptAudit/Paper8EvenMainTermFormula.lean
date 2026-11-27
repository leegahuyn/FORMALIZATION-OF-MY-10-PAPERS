import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenDenominatorWeightLimits

/-! The exact signed linear combination of the four progression constants. -/

namespace ManuscriptAudit.Paper8EvenMainTermFormula

open Paper8EvenDenominatorWeightLimits

noncomputable section

theorem four_progression_main_term (A : ℕ → ℂ) :
    (∑ r ∈ Finset.range 4, evenWeightLimit r * A r) =
      A 0 * alternatingWeight + A 2 * zetaWeight +
        (A 1 + A 3) * inversePower 2 * alternatingWeight +
        (A 3 - A 1) * betaWeight := by
  let F (r : ℕ) := evenWeightLimit r * A r
  have h : (∑ r ∈ Finset.range 4, F r) = F 0 + F 1 + F 2 + F 3 := by
    calc
      _ = (∑ r ∈ Finset.range 3, F r) + F 3 := Finset.sum_range_succ F 3
      _ = _ := by
        rw [Finset.sum_range_succ F 2, Finset.sum_range_succ F 1, Finset.sum_range_succ F 0]
        simp
  change (∑ r ∈ Finset.range 4, F r) = _
  rw [h]
  unfold F
  rw [even_weight_limit_zero_class (D := 0) (by decide),
    even_weight_limit_one_class (D := 1) (by decide),
    even_weight_limit_two_class (D := 2) (by decide),
    even_weight_limit_three_class (D := 3) (by decide)]
  ring

end
end ManuscriptAudit.Paper8EvenMainTermFormula

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper8EvenMainTermFormula.four_progression_main_term
  let axioms ← collectAxioms name
  let bad := axioms.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {axioms}"
