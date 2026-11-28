import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import PrimalitySheafVerification.ManuscriptAudit.Paper4FiniteSupportProgression

/-! The actual prime support determined by gcd and discriminant has a
finite description. A reduced congruence class still contains arbitrarily
large primes after deleting that specified support. -/

namespace ManuscriptAudit.Paper4ExceptionalPrimeProgression

open Paper4FiniteSupportProgression (progression)

def exceptional (g d : ℕ) : Finset ℕ :=
  g.primeFactors ∪ d.primeFactors

theorem prime_mem_exceptional_iff {g d p : ℕ}
    (hg : g ≠ 0) (hd : d ≠ 0) (hp : p.Prime) :
    p ∈ exceptional g d ↔ p ∣ g ∨ p ∣ d := by
  simp [exceptional, Nat.mem_primeFactors, hg, hd, hp]

/-- The positive existence statement holds in any reduced progression,
including those that also contain some smaller exceptional primes. -/
theorem exists_large_prime_avoiding_support {a q : ℕ} (hq : q ≠ 0) (hC : a.Coprime q)
    (S : Finset ℕ) (B : ℕ) :
    ∃ p > B, p ∈ progression a q ∧ p ∉ S := by
  obtain ⟨p, hSize, hPrime, hClass⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (S.sup id)) hq hC
  refine ⟨p, (le_max_left _ _).trans_lt hSize, ⟨hPrime, hClass⟩, ?_⟩
  intro hpS
  have hBound : p ≤ S.sup id := Finset.le_sup (f := id) hpS
  exact (hBound.trans (le_max_right _ _)).not_gt hSize

theorem exists_large_good_prime {a q g d : ℕ} (hq : q ≠ 0) (hC : a.Coprime q)
    (hg : g ≠ 0) (hd : d ≠ 0) (B : ℕ) :
    ∃ p > B, p.Prime ∧ p ≡ a [MOD q] ∧ ¬ p ∣ g ∧ ¬ p ∣ d := by
  obtain ⟨p, hB, ⟨hp, hMod⟩, hS⟩ :=
    exists_large_prime_avoiding_support hq hC (exceptional g d) B
  have hNot := (not_congr (prime_mem_exceptional_iff hg hd hp)).mp hS
  exact ⟨p, hB, hp, hMod, fun h ↦ hNot (Or.inl h), fun h ↦ hNot (Or.inr h)⟩

end ManuscriptAudit.Paper4ExceptionalPrimeProgression

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4ExceptionalPrimeProgression.prime_mem_exceptional_iff,
      ``ManuscriptAudit.Paper4ExceptionalPrimeProgression.exists_large_prime_avoiding_support,
      ``ManuscriptAudit.Paper4ExceptionalPrimeProgression.exists_large_good_prime] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
