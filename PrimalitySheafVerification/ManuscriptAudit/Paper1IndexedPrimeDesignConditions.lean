import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Prime.Nth
import PrimalitySheafVerification.ManuscriptAudit.Paper1IndexedPrimeUniformDesign

/-! Exact conditions for the indexed-prime design and for an additional linear congruence. -/

namespace ManuscriptAudit.Paper1IndexedPrimeDesignConditions

open Paper1IndexedPrimeValuation Paper1IndexedPrimeUniformDesign

/-- The first three primes are enumerated from index zero in the native enumeration. -/
theorem third_prime : Nat.nth Nat.Prime (3 - 1) = 5 :=
  Nat.nth_prime_two_eq_five

/-- For two prime coefficients, the only obstruction at positive precision is one common prime. -/
theorem prime_term_design_iff {p q A k : ℕ} [Fact p.Prime] (hq : q.Prime)
    (hA : ¬ p ∣ A) (hk : 0 < k) (b : ℤ) :
    (∃ y : ℤ, ∀ j : ℕ, padicNorm p (term A q j b y) ≤ (p : ℚ)^(-(k : ℤ))) ↔
      (p = q → (p : ℤ) ∣ b) := by
  rw [exists_term_bound_iff hA q k b, ← Nat.cast_pow]
  change ((Nat.gcd (p ^ k) q : ℕ) : ℤ) ∣ b ↔ _
  by_cases heq : p = q
  · subst q
    have hp : p ∣ p ^ k := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      exact ⟨p ^ j, by rw [pow_succ']⟩
    have hg : (p ^ k).gcd p = p :=
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd hp (dvd_refl p))
    simp [hg]
  · have hp : p.Prime := Fact.out
    have hcop : Nat.Coprime (p ^ k) q := ((Nat.coprime_primes hp hq).mpr heq).pow_left _
    have hg : (p ^ k).gcd q = 1 := hcop
    simp [hg, heq]

/-- Imposing y ≡ y₀ mod N leaves an exact gcd divisibility condition, even for shared factors. -/
theorem linear_residue_with_progression (modulus q b N y₀ : ℤ) :
    (∃ y : ℤ, modulus ∣ q * y + b ∧ N ∣ y - y₀) ↔
      (Int.gcd modulus (q * N) : ℤ) ∣ q * y₀ + b := by
  rw [← linear_residue_solvable modulus (q * N) (q * y₀ + b)]
  constructor
  · rintro ⟨y, hy, z, hz⟩
    have hyz : y = y₀ + N * z := by linarith
    refine ⟨z, ?_⟩
    rw [hyz] at hy
    convert hy using 1 <;> ring
  · rintro ⟨z, hz⟩
    refine ⟨y₀ + N * z, ?_, ⟨z, by ring⟩⟩
    convert hz using 1 <;> ring

end ManuscriptAudit.Paper1IndexedPrimeDesignConditions

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper1IndexedPrimeDesignConditions.third_prime,
      ``ManuscriptAudit.Paper1IndexedPrimeDesignConditions.prime_term_design_iff,
      ``ManuscriptAudit.Paper1IndexedPrimeDesignConditions.linear_residue_with_progression] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
