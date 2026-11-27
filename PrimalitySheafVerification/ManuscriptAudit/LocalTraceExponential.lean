import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed

/-! The convergent scalar trace expansion underlying the finite local determinant. -/

namespace ManuscriptAudit.LocalTraceExponential

open Set Filter
open scoped Topology

noncomputable section

def term (n : ℕ) (z : ℂ) : ℂ := z ^ (n + 1) / ((n + 1 : ℕ) : ℂ)

def traceLog (z : ℂ) : ℂ := ∑' n : ℕ, term n z

private theorem term_norm_bound {r : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖term n z‖ ≤ r ^ (n + 1) := by
  have hd : 1 ≤ ‖((n + 1 : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  calc
    _ ≤ ‖z ^ (n + 1)‖ := by
      rw [term, norm_div]
      exact div_le_self (norm_nonneg _) hd
    _ ≤ _ := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg z) hz _

private theorem shifted_geometric_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun n : ℕ => r ^ (n + 1)) := by
  simpa only [pow_succ'] using (summable_geometric_of_lt_one hr h₁).mul_left r

theorem term_norm_summable {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun n => ‖term n z‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_norm_bound le_rfl)
    (shifted_geometric_summable (norm_nonneg _) hz)

theorem traceLog_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => term n z) (-Complex.log (1 - z)) := by
  let f : ℕ → ℂ := fun n => z ^ n / (n : ℂ)
  change HasSum (fun n => f (n + 1)) (-Complex.log (1 - z))
  apply (hasSum_nat_add_iff (f := f) 1).mpr
  simpa only [Finset.sum_range_one, f, Nat.cast_zero, div_zero, add_zero] using
    Complex.hasSum_taylorSeries_neg_log hz

private theorem one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have he : z = 1 := (sub_eq_zero.mp h).symm
  simpa [he] using hz

theorem exp_traceLog {z : ℂ} (hz : ‖z‖ < 1) : Complex.exp (traceLog z) = (1 - z)⁻¹ := by
  rw [traceLog, (traceLog_hasSum hz).tsum_eq, Complex.exp_neg, Complex.exp_log (one_sub_ne_zero hz)]

end
end ManuscriptAudit.LocalTraceExponential

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.LocalTraceExponential.term_norm_summable,
      ``ManuscriptAudit.LocalTraceExponential.traceLog_hasSum,
      ``ManuscriptAudit.LocalTraceExponential.exp_traceLog] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
