import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Prime.Nth
import PrimalitySheafVerification.ManuscriptAudit.CubicHasseBound
import PrimalitySheafVerification.ManuscriptAudit.Paper7CommonEulerContinuity

/-! The actual good-prime elliptic local factors in the common argument of physical pp. 280–281. -/

namespace ManuscriptAudit.Paper7ActualCommonEuler

open Filter Topology Paper7CommonEulerPointwise
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

def goodPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 2)

theorem goodPrime_prime (n : ℕ) : (goodPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

theorem goodPrime_atLeastFive (n : ℕ) : 5 ≤ goodPrime n := by
  rw [← Nat.nth_prime_two_eq_five]
  exact (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (by omega)

theorem goodPrime_tendsto : Tendsto (fun n => (goodPrime n : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro x
  obtain ⟨m, hm⟩ := exists_nat_ge x
  filter_upwards [eventually_ge_atTop m] with n hn
  have hIndex : n + 2 ≤ goodPrime n :=
    Nat.le_nth (fun hf => (Nat.infinite_setOf_prime hf).elim)
  refine hm.trans ?_
  exact_mod_cast hn.trans (by omega : n ≤ goodPrime n)

/-- The actual signed projective point count at the paper's displayed coefficient A=1. -/
def signedTrace (n : ℕ) : ℤ :=
  (goodPrime n : ℤ) + 1 -
    (Nat.card (paper5TraceCurve (goodPrime n) (-1)).toProjective.Point : ℤ)

abbrev trace (n : ℕ) : ℂ := signedTrace n

theorem trace_hasse (n : ℕ) : ‖trace n‖ ≤ 2 * Real.sqrt (goodPrime n : ℝ) := by
  letI : Fact (goodPrime n).Prime := ⟨goodPrime_prime n⟩
  have h := CubicHasseBound.paper5_printed_reduction_hasse (goodPrime n)
    (goodPrime_atLeastFive n) (A := (-1 : ZMod (goodPrime n))) (neg_ne_zero.mpr one_ne_zero)
  have he : trace n = Complex.ofReal ((goodPrime n : ℝ) + 1 -
      (Nat.card (paper5TraceCurve (goodPrime n) (-1)).toProjective.Point : ℝ)) := by
    simp only [trace, signedTrace, Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_natCast,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- The pointwise common-argument limit of the actual displayed local factors is discontinuous. -/
theorem actual_no_continuous_common_argument {r : ℝ} (hr : 0 < r) :
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g 0 ∧
      ∀ z : ℂ, ‖z‖ < r → Tendsto (partialProduct goodPrime trace z) atTop (𝓝 (g z)) :=
  Paper7CommonEulerContinuity.no_continuous_pointwise_limit goodPrime_tendsto trace_hasse hr

end
end ManuscriptAudit.Paper7ActualCommonEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7ActualCommonEuler.goodPrime_prime,
      ``ManuscriptAudit.Paper7ActualCommonEuler.goodPrime_atLeastFive,
      ``ManuscriptAudit.Paper7ActualCommonEuler.goodPrime_tendsto,
      ``ManuscriptAudit.Paper7ActualCommonEuler.trace_hasse,
      ``ManuscriptAudit.Paper7ActualCommonEuler.actual_no_continuous_common_argument] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
