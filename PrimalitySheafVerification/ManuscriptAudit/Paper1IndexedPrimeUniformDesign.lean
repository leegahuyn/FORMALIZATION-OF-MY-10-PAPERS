import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import PrimalitySheafVerification.ManuscriptAudit.Paper1IndexedPrimeValuation

/-! For m = 1, the literal indexed-prime valuation budget is exactly a linear congruence. -/

namespace ManuscriptAudit.Paper1IndexedPrimeUniformDesign

open Paper1IndexedPrimeValuation

variable {p : ℕ} [Fact p.Prime]

/-- The actual rational term for m = 1, with q the printed indexed prime and b = ±(A − 1). -/
def term (A q j : ℕ) (b y : ℤ) : ℚ :=
  ((q : ℤ) * y + b : ℤ) * ((A + 1).choose j : ℚ) / (A : ℚ)^q

private theorem unit_power_norm {A : ℕ} (hA : ¬ p ∣ A) (q : ℕ) :
    padicNorm p ((A : ℚ)^q) = 1 := by
  induction q with
  | zero => rw [pow_zero, padicNorm.one]
  | succ q h =>
    rw [pow_succ, padicNorm.mul, h, (padicNorm.nat_eq_one_iff A).mpr hA, mul_one]

/-- Since S₀(A) = 1, the norm bound on every term holds exactly at the intended congruence. -/
theorem term_bound_iff {A : ℕ} (hA : ¬ p ∣ A) (q k : ℕ) (b y : ℤ) :
    (∀ j : ℕ, padicNorm p (term A q j b y) ≤ (p : ℚ)^(-(k : ℤ))) ↔
      (p : ℤ)^k ∣ (q : ℤ) * y + b := by
  rw [← Nat.cast_pow]
  rw [padicNorm.dvd_iff_norm_le]
  constructor
  · intro h
    simpa only [term, Nat.choose_zero_right, Nat.cast_one, mul_one, padicNorm.div,
      unit_power_norm hA q, div_one] using h 0
  · intro h j
    rw [term, padicNorm.div, unit_power_norm hA q, div_one, padicNorm.mul]
    exact (mul_le_of_le_one_right (padicNorm.nonneg _) (padicNorm.of_nat _)).trans h

/-- This is the exact criterion for a valuation budget at every j in the unit-denominator case. -/
theorem exists_term_bound_iff {A : ℕ} (hA : ¬ p ∣ A) (q k : ℕ) (b : ℤ) :
    (∃ y : ℤ, ∀ j : ℕ, padicNorm p (term A q j b y) ≤ (p : ℚ)^(-(k : ℤ))) ↔
      (Int.gcd ((p : ℤ)^k) (q : ℤ) : ℤ) ∣ b := by
  simp_rw [term_bound_iff hA q k b]
  exact linear_residue_solvable ((p : ℤ)^k) q b

end ManuscriptAudit.Paper1IndexedPrimeUniformDesign

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper1IndexedPrimeUniformDesign.term_bound_iff,
      ``ManuscriptAudit.Paper1IndexedPrimeUniformDesign.exists_term_bound_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
