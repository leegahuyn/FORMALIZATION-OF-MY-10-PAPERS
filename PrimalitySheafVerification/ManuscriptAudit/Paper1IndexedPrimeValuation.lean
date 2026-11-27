import Lean.Util.CollectAxioms
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! The physical p. 10 statements use an indexed prime in the modulus and a prime power in the proof. -/

namespace ManuscriptAudit.Paper1IndexedPrimeValuation

/-- A linear congruence with the printed coefficient is solvable exactly under the gcd condition. -/
theorem linear_residue_solvable (modulus q b : ℤ) :
    (∃ y : ℤ, modulus ∣ q * y + b) ↔ (Int.gcd modulus q : ℤ) ∣ b := by
  constructor
  · rintro ⟨y, hy⟩
    have hm : (Int.gcd modulus q : ℤ) ∣ modulus := Int.gcd_dvd_left _ _
    have hq : (Int.gcd modulus q : ℤ) ∣ q := Int.gcd_dvd_right _ _
    have hb : (Int.gcd modulus q : ℤ) ∣ (q * y + b) - q * y :=
      dvd_sub (dvd_trans hm hy) (dvd_mul_of_dvd_left hq y)
    rwa [add_sub_cancel_left] at hb
  · rintro ⟨t, ht⟩
    refine ⟨-(Int.gcdB modulus q * t), Int.gcdA modulus q * t, ?_⟩
    rw [ht, Int.gcd_eq_gcd_ab]
    ring

/-- With a prime as coefficient, cancel exactly one power of that prime. -/
theorem equal_prime_residue (p : ℤ) (hp : p ≠ 0) (e : ℕ) (y u : ℤ) :
    p ^ (e + 1) ∣ p * y + p * u ↔ p ^ e ∣ y + u := by
  rw [pow_succ', ← mul_add]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, mul_left_cancel₀ hp ?_⟩
    simpa only [mul_assoc] using hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hx, mul_assoc]

/-- In Prop. 2.4(a), take p = p₃ = 5, A = 6, and y = 4 in the plus case. -/
theorem printed_low_branch_fails :
    Nat.Coprime 6 5 ∧ padicValInt 5 ((6 : ℤ) - 1) = 1 ∧
      padicValInt 5 ((6 : ℤ) - 1) < 3 ∧
      padicValInt 5 (5 * (4 : ℤ) + (6 - 1)) = 2 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  change Nat.Coprime 6 5 ∧ padicValNat 5 5 = 1 ∧ padicValNat 5 5 < 3 ∧
    padicValNat 5 (5 ^ 2) = 2
  simp only [padicValNat_self, padicValNat.prime_pow]
  decide

/-- In Prop. 2.4(b), take p = p₃ = 5, A = 126, n = t = 3 and σ = 4. -/
theorem printed_high_residue_fails :
    Nat.Coprime 126 5 ∧ padicValInt 5 ((126 : ℤ) - 1) = 3 ∧
      ∀ y : ℤ, (5 : ℤ) ∣ y + 1 → ¬ (5 : ℤ)^4 ∣ 5 * y + (126 - 1) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨by decide, ?_, ?_⟩
  · change padicValNat 5 (5 ^ 3) = 3
    rw [padicValNat.prime_pow]
  · intro y
    rintro ⟨r, hr⟩ ⟨s, hs⟩
    norm_num at hs
    omega

end ManuscriptAudit.Paper1IndexedPrimeValuation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper1IndexedPrimeValuation.linear_residue_solvable,
      ``ManuscriptAudit.Paper1IndexedPrimeValuation.equal_prime_residue,
      ``ManuscriptAudit.Paper1IndexedPrimeValuation.printed_low_branch_fails,
      ``ManuscriptAudit.Paper1IndexedPrimeValuation.printed_high_residue_fails] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
