import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecificLimits.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper7CommonEulerLocalDecay

/-! The elliptic Euler partial products at a common parameter have a discontinuous pointwise limit. -/

namespace ManuscriptAudit.Paper7CommonEulerPointwise

open Filter Topology Paper7CommonEulerLocalDecay

noncomputable section

def partialProduct (q : ℕ → ℕ) (a : ℕ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ Finset.range n, (denominator (q i) (a i) z)⁻¹

@[simp] theorem partialProduct_zero_argument (q : ℕ → ℕ) (a : ℕ → ℂ) (n : ℕ) :
    partialProduct q a 0 n = 1 := by
  simp [partialProduct, denominator]

theorem tendsto_at_nonzero {q : ℕ → ℕ} {a : ℕ → ℂ}
    (hq : Tendsto (fun n => (q n : ℝ)) atTop atTop)
    (hHasse : ∀ n, ‖a n‖ ≤ 2 * Real.sqrt (q n : ℝ)) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (partialProduct q a z) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_factor_norm_le_half hq hHasse hz)
  let C : ℝ := ‖partialProduct q a z N‖
  have hNorm (n : ℕ) : ‖partialProduct q a z (N + n)‖ ≤ C * (1 / 2 : ℝ)^n := by
    induction n with
    | zero => simp [C]
    | succ n ih =>
      have hStep : partialProduct q a z (N + (n + 1)) =
          partialProduct q a z (N + n) * (denominator (q (N + n)) (a (N + n)) z)⁻¹ := by
        simp only [Nat.add_succ, partialProduct, Finset.prod_range_succ]
      rw [hStep, norm_mul, pow_succ, ← mul_assoc]
      exact mul_le_mul ih (hN (N + n) (by omega)) (norm_nonneg _) (by positivity)
  have hPow : Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hL : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hPow
  rw [Metric.tendsto_atTop] at hL ⊢
  intro ε hε
  obtain ⟨M, hM⟩ := hL ε hε
  refine ⟨N + M, fun n hn => ?_⟩
  have hK : M ≤ n - N := by omega
  have hn' : N + (n - N) = n := by omega
  have h₀ := hNorm (n - N)
  rw [hn'] at h₀
  rw [dist_zero_right]
  apply h₀.trans_lt
  have hp : 0 ≤ C * (1 / 2 : ℝ)^(n - N) := by positivity
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hp] using hM (n - N) hK

end
end ManuscriptAudit.Paper7CommonEulerPointwise

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper7CommonEulerPointwise.partialProduct_zero_argument,
      ``ManuscriptAudit.Paper7CommonEulerPointwise.tendsto_at_nonzero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
