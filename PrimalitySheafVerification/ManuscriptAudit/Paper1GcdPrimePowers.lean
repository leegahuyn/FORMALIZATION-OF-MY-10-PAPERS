import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing

/-! The common residue factors are the prime powers with the minimum
of the two native valuations printed in the manuscript. -/

namespace ManuscriptAudit.Paper1GcdPrimePowers

open Function
open scoped BigOperators

variable (m n : ℕ)

abbrev localModulus (p : n.primeFactors) : ℕ :=
  (p : ℕ) ^ min (m.factorization p) (n.factorization p)

theorem gcd_eq_prod (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.gcd m n = ∏ p : n.primeFactors, localModulus m n p := by
  classical
  have hG : Nat.gcd m n ≠ 0 :=
    (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)).ne'
  have hs : (Nat.gcd m n).primeFactors ⊆ n.primeFactors := by
    change (Nat.gcd m n).factorization.support ⊆ n.factorization.support
    rw [Nat.factorization_gcd hm hn]
    exact Finsupp.support_mono inf_le_right
  have hp : Nat.gcd m n = ∏ p ∈ n.primeFactors, p ^ (Nat.gcd m n).factorization p := by
    calc
      Nat.gcd m n = ∏ p ∈ (Nat.gcd m n).primeFactors, p ^ (Nat.gcd m n).factorization p :=
        Nat.prod_primeFactors_pow_factorization hG
      _ = ∏ p ∈ n.primeFactors, p ^ (Nat.gcd m n).factorization p := by
        apply Finset.prod_subset hs
        intro p _ h
        have hz : (Nat.gcd m n).factorization p = 0 := Finsupp.notMem_support_iff.mp h
        rw [hz, pow_zero]
  calc
    Nat.gcd m n = ∏ p ∈ n.primeFactors, p ^ min (m.factorization p) (n.factorization p) := by
      simpa only [Nat.factorization_gcd hm hn, Finsupp.inf_apply] using hp
    _ = ∏ p : n.primeFactors, localModulus m n p :=
      (Finset.prod_coe_sort _ _).symm

theorem gcd_prime_power (hm : m ≠ 0) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.gcd m (p ^ k) = p ^ min (m.factorization p) k := by
  have hG := (Nat.gcd_pos_of_pos_left (p ^ k) (Nat.pos_of_ne_zero hm)).ne'
  apply Nat.eq_of_factorization_eq' hG (pow_ne_zero _ hp.ne_zero)
  rw [Nat.factorization_gcd hm (pow_ne_zero _ hp.ne_zero),
    hp.factorization_pow, hp.factorization_pow]
  ext q
  by_cases hq : q = p
  · subst q
    simp
  · simp [Finsupp.single_apply, hq, Ne.symm hq]

theorem gcd_prime_power_valuation (hm : m ≠ 0) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.gcd m (p ^ k) = p ^ min (padicValNat p m) k := by
  rw [gcd_prime_power m hm hp, Nat.factorization_def m hp]

theorem localModulus_pairwise :
    Pairwise (Nat.Coprime on localModulus m n) := by
  intro p q hpq
  refine Nat.Coprime.pow _ _ ((Nat.coprime_primes ?_ ?_).mpr (Subtype.coe_ne_coe.mpr hpq))
  · exact Nat.prime_of_mem_primeFactors p.2
  · exact Nat.prime_of_mem_primeFactors q.2

/-- The entire common modulus, including its zero-exponent local
factors, is the literal native CRT product. -/
noncomputable def residueEquivPrimePowers (hm : m ≠ 0) (hn : n ≠ 0) :
    ZMod (Nat.gcd m n) ≃+* (∀ p : n.primeFactors, ZMod (localModulus m n p)) :=
  (ZMod.ringEquivCongr (gcd_eq_prod m n hm hn)).trans
    (ZMod.prodEquivPi (localModulus m n) (localModulus_pairwise m n))

end ManuscriptAudit.Paper1GcdPrimePowers

open Lean Elab Command in
run_cmd do
  let names := [``ManuscriptAudit.Paper1GcdPrimePowers.gcd_eq_prod,
    ``ManuscriptAudit.Paper1GcdPrimePowers.gcd_prime_power_valuation,
    ``ManuscriptAudit.Paper1GcdPrimePowers.residueEquivPrimePowers]
  for name in names do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
