import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.Paper4MangoldtPole

/-! Removing the actual higher prime powers from the residue-class von
Mangoldt series preserves the polar term and its bounded real error. -/

namespace ManuscriptAudit.Paper4PrimeLogWeightPole

open ArithmeticFunction.vonMangoldt Paper4MangoldtPole LSeries

noncomputable section

variable {q : ℕ} [NeZero q] (a : ZMod q)

def primeWeight (s : ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ s

private def nonprimeWeight (s : ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ s

def primeSeries (s : ℝ) : ℝ := ∑' n, primeWeight a s n

private theorem nonprime_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ nonprimeWeight a s n := by
  apply div_nonneg _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  split_ifs <;> simp [residueClass_nonneg]

private theorem nonprime_le_one {s : ℝ} (hs : 1 ≤ s) (n : ℕ) :
    nonprimeWeight a s n ≤ nonprimeWeight a 1 n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [nonprimeWeight]
  · unfold nonprimeWeight
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    have h₁ : 1 ≤ n := hn
    have h₀ : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h₁
    apply div_le_div_of_nonneg_left _ (Real.rpow_pos_of_pos hp _)
      (Real.rpow_le_rpow_of_exponent_le h₀ hs)
    split_ifs <;> simp [residueClass_nonneg]

private theorem nonprime_summable_one : Summable (nonprimeWeight a 1) := by
  change Summable (fun n : ℕ ↦ (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ (1 : ℝ))
  simpa only [Real.rpow_one] using summable_residueClass_non_primes_div a

private theorem nonprime_summable {s : ℝ} (hs : 1 ≤ s) : Summable (nonprimeWeight a s) :=
  (nonprime_summable_one a).of_nonneg_of_le (nonprime_nonneg a s) (nonprime_le_one a hs)

private theorem prime_sub_nonprime (s : ℝ) (n : ℕ) :
    residueClass a n / (n : ℝ) ^ s - nonprimeWeight a s n = primeWeight a s n := by
  by_cases h : n.Prime <;> simp [primeWeight, nonprimeWeight, h]

theorem primeWeight_summable {s : ℝ} (hs : 1 < s) : Summable (primeWeight a s) :=
  ((realSeries_summable a hs).sub (nonprime_summable a hs.le)).congr
    (prime_sub_nonprime a s)

theorem primeSeries_sub_full {s : ℝ} (hs : 1 < s) :
    primeSeries a s = realSeries a s - ∑' n, nonprimeWeight a s n := by
  unfold primeSeries realSeries
  rw [← (realSeries_summable a hs).tsum_sub (nonprime_summable a hs.le)]
  exact tsum_congr fun n ↦ (prime_sub_nonprime a s n).symm

/-- The genuine logarithm-weighted prime series has the same principal part. -/
theorem bounded_prime_pole_error (ha : IsUnit a) :
    ∃ B : ℝ, ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      |primeSeries a s - (q.totient : ℝ)⁻¹ / (s - 1)| ≤ B := by
  obtain ⟨B, hB⟩ := bounded_real_pole_error a ha
  refine ⟨B + (∑' n, nonprimeWeight a 1 n), fun s hs ↦ ?_⟩
  have hLower : 0 ≤ ∑' n, nonprimeWeight a s n := tsum_nonneg (nonprime_nonneg a s)
  have hUpper : (∑' n, nonprimeWeight a s n) ≤ ∑' n, nonprimeWeight a 1 n :=
    Summable.tsum_le_tsum (nonprime_le_one a hs.1.le)
      (nonprime_summable a hs.1.le) (nonprime_summable_one a)
  rw [primeSeries_sub_full a hs.1]
  calc
    _ = |(realSeries a s - (q.totient : ℝ)⁻¹ / (s - 1)) +
      -(∑' n, nonprimeWeight a s n)| := by congr 1; ring
    _ ≤ |realSeries a s - (q.totient : ℝ)⁻¹ / (s - 1)| +
        |-(∑' n, nonprimeWeight a s n)| := abs_add_le _ _
    _ ≤ _ := by rw [abs_neg, abs_of_nonneg hLower]; exact add_le_add (hB s hs) hUpper

end
end ManuscriptAudit.Paper4PrimeLogWeightPole

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4PrimeLogWeightPole.primeWeight_summable,
      ``ManuscriptAudit.Paper4PrimeLogWeightPole.primeSeries_sub_full,
      ``ManuscriptAudit.Paper4PrimeLogWeightPole.bounded_prime_pole_error] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
