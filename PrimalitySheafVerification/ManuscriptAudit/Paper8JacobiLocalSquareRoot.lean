import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8JacobiPrimeBound
import PrimalitySheafVerification.ManuscriptAudit.Paper8JacobiPrimePowerBound

/-! Uniform square-root bound for the genuine Jacobi-twisted unit sum on every odd prime power. -/

namespace ManuscriptAudit.Paper8JacobiLocalSquareRoot

open Paper8JacobiPrimeBound Paper8JacobiPrimePowerBound Paper8OddCrossJacobiSum
open Paper8ZModAdditiveCRT

noncomputable section

private def LocalSquareRootBound (N : ℕ) : Prop :=
  ∀ [NeZero N] (a : ZMod N), IsUnit a →
    ‖twistedSymmetricUnitSum (jacobiUnitWeight N) a‖ ≤ 2 * Real.sqrt (N : ℝ)

private theorem local_even {p r : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hr : 0 < r) :
    LocalSquareRootBound (p ^ r * p ^ r) := by
  intro _ a ha
  have h := norm_jacobi_sum_even_prime_power hp hr a ha
  have hS : Real.sqrt ((p ^ r * p ^ r : ℕ) : ℝ) = ((p ^ r : ℕ) : ℝ) := by
    rw [Nat.cast_mul, ← pow_two, Real.sqrt_sq (Nat.cast_nonneg _)]
  rwa [hS]

private theorem local_odd {p r : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hr : 0 < r) :
    LocalSquareRootBound (p ^ r * (p * p ^ r)) := by
  intro _ a ha
  have h := norm_jacobi_sum_odd_prime_power hp hr a ha
  have hS : Real.sqrt ((p ^ r * (p * p ^ r) : ℕ) : ℝ) = ((p ^ r : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
    rw [show p ^ r * (p * p ^ r) = p * (p ^ r * p ^ r) by ring,
      Nat.cast_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p), ← pow_two, Real.sqrt_sq (Nat.cast_nonneg _)]
    ring
  rw [hS, ← mul_assoc]
  exact h

private theorem local_prime_power {p n : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hn : 0 < n) :
    LocalSquareRootBound (p ^ n) := by
  by_cases h1 : n = 1
  · subst n
    simpa only [pow_one] using (show LocalSquareRootBound p from fun a ha => norm_jacobi_sum_prime hp a ha)
  let r := n / 2
  have hr : 0 < r := by dsimp only [r]; omega
  by_cases hE : n % 2 = 0
  · have he : n = r + r := by dsimp only [r]; omega
    have hN : p ^ n = p ^ r * p ^ r := by rw [← pow_add, ← he]
    rw [hN]
    exact local_even (p := p) hp hr
  · have he : n = r + (1 + r) := by dsimp only [r]; omega
    have hN : p ^ n = p ^ r * (p * p ^ r) := by
      rw [he, pow_add, pow_add, pow_one]
    rw [hN]
    exact local_odd (p := p) hp hr

theorem norm_jacobi_sum_prime_power {p n : ℕ} [Fact p.Prime] [NeZero (p ^ n)]
    (hp : p ≠ 2) (hn : 0 < n) (a : ZMod (p ^ n)) (ha : IsUnit a) :
    ‖twistedSymmetricUnitSum (jacobiUnitWeight (p ^ n)) a‖ ≤ 2 * Real.sqrt ((p ^ n : ℕ) : ℝ) :=
  local_prime_power hp hn a ha

end
end ManuscriptAudit.Paper8JacobiLocalSquareRoot

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8JacobiLocalSquareRoot.norm_jacobi_sum_prime_power
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
