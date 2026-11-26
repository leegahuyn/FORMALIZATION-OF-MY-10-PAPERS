import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.NormNum

/-!
# The finite prime sample in Paper 6

The worked model on physical p. 202 requires p to be a good simple
prime and uses a finite sample T of good simple primes. Its last gcd
equality also requires p ∈ T. The linear polynomial X gives an
actual example in which both 2 and 3 are good simple primes and
T = {3}, so the displayed equality at p = 2 fails.
-/

namespace ManuscriptAudit.FinitePrimeSample

open Polynomial
open scoped BigOperators

/-- The product of the members of the finite prime sample. -/
def chartModulus (T : Finset ℕ) : ℕ := ∏ q ∈ T, q

theorem prime_dvd_chartModulus_iff (p : ℕ) (hp : Nat.Prime p) (T : Finset ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) :
    p ∣ chartModulus T ↔ p ∈ T := by
  classical
  unfold chartModulus
  induction T using Finset.induction_on with
  | empty => simp [hp.ne_one]
  | @insert q T hq ih =>
    have hPrimeQ := hT q (Finset.mem_insert_self q T)
    have hPrimeT : ∀ r ∈ T, Nat.Prime r := fun r hr => hT r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hq, hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp hPrimeQ,
      ih hPrimeT, Finset.mem_insert]

theorem chart_gcd_eq_prime_iff (p : ℕ) (hp : Nat.Prime p) (T : Finset ℕ)
    (hT : ∀ q ∈ T, Nat.Prime q) :
    Nat.gcd (chartModulus T) p = p ↔ p ∈ T :=
  Nat.gcd_eq_right_iff_dvd.trans (prime_dvd_chartModulus_iff p hp T hT)

/-- The monic linear polynomial X has resultant with its derivative equal to 1. -/
theorem X_derivative_resultant :
    resultant (X : ℤ[X]) (derivative X) 1 0 = 1 := by
  simp

/-- The residue polynomial X has the simple root 0 at every rational prime. -/
theorem X_simple_root_mod_prime (p : ℕ) [Fact (Nat.Prime p)] :
    let f := (X : ℤ[X]).map (Int.castRingHom (ZMod p))
    f.eval 0 = 0 ∧ (derivative f).eval 0 ≠ 0 := by
  simp

/-- A genuine sample of good simple primes that disproves the printed gcd equality. -/
theorem paper6_worked_model_gcd_refuted :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.gcd (chartModulus {3}) 2 ≠ 2 := by
  refine ⟨by decide, by decide, ?_⟩
  norm_num [chartModulus, Nat.gcd]

end ManuscriptAudit.FinitePrimeSample

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FinitePrimeSample.prime_dvd_chartModulus_iff,
      ``ManuscriptAudit.FinitePrimeSample.chart_gcd_eq_prime_iff,
      ``ManuscriptAudit.FinitePrimeSample.X_derivative_resultant,
      ``ManuscriptAudit.FinitePrimeSample.X_simple_root_mod_prime,
      ``ManuscriptAudit.FinitePrimeSample.paper6_worked_model_gcd_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
