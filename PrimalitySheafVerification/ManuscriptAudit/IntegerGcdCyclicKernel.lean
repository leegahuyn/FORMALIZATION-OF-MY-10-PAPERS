import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

/-! The exact integral divisibility tests underlying the cyclic Tor computation. -/

namespace ManuscriptAudit.IntegerGcdCyclicKernel

variable {m n : ℕ}

/-- The cofactor of the positive gcd divides exactly those representatives
whose product by the second integer is divisible by the first integer. -/
theorem cofactor_dvd_iff (hm : 0 < m) (a : ℤ) :
    ((m / Nat.gcd m n : ℕ) : ℤ) ∣ a ↔ (m : ℤ) ∣ (n : ℤ) * a := by
  have hgN : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  have hg : (Nat.gcd m n : ℤ) ≠ 0 := by exact_mod_cast hgN.ne'
  have hmZ : (Nat.gcd m n : ℤ) * ((m / Nat.gcd m n : ℕ) : ℤ) = m := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  obtain ⟨l, hl⟩ := Nat.gcd_dvd_right m n
  have hlZ : (n : ℤ) = (Nat.gcd m n : ℤ) * (l : ℤ) := by exact_mod_cast hl
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨(l : ℤ) * q, ?_⟩
    calc
      (n : ℤ) * a =
          ((Nat.gcd m n : ℤ) * l) * (((m / Nat.gcd m n : ℕ) : ℤ) * q) := by
        rw [← hlZ, ← hq]
      _ = ((Nat.gcd m n : ℤ) * ((m / Nat.gcd m n : ℕ) : ℤ)) * (l * q) := by ring
      _ = (m : ℤ) * (l * q) := by rw [hmZ]
  · rintro ⟨q, hq⟩
    have hd : (m : ℤ) ∣ (Nat.gcd m n : ℤ) * a := by
      rw [Nat.gcd_eq_gcd_ab, add_mul]
      apply Int.dvd_add
      · exact ⟨Nat.gcdA m n * a, by ring⟩
      · refine ⟨Nat.gcdB m n * q, ?_⟩
        calc
          (n : ℤ) * Nat.gcdB m n * a = Nat.gcdB m n * ((n : ℤ) * a) := by ring
          _ = (m : ℤ) * (Nat.gcdB m n * q) := by rw [hq]; ring
    obtain ⟨b, hb⟩ := hd
    refine ⟨b, mul_left_cancel₀ hg ?_⟩
    calc
      (Nat.gcd m n : ℤ) * a = (m : ℤ) * b := hb
      _ = (Nat.gcd m n : ℤ) * (((m / Nat.gcd m n : ℕ) : ℤ) * b) := by
        rw [← mul_assoc, hmZ]

/-- Multiplication by the cofactor has, modulo the first modulus, exactly the
gcd as its period on the integers. -/
theorem gcd_dvd_iff_cofactor_mul (hm : 0 < m) (a : ℤ) :
    (Nat.gcd m n : ℤ) ∣ a ↔ (m : ℤ) ∣ ((m / Nat.gcd m n : ℕ) : ℤ) * a := by
  have hmZ : ((m / Nat.gcd m n : ℕ) : ℤ) * (Nat.gcd m n : ℤ) = m := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left m n)
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hc : ((m / Nat.gcd m n : ℕ) : ℤ) ≠ 0 := by
    intro he
    apply hm0
    rw [← hmZ, he, zero_mul]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, by rw [← mul_assoc, hmZ]⟩
  · rintro ⟨q, hq⟩
    refine ⟨q, mul_left_cancel₀ hc ?_⟩
    rw [← mul_assoc, hmZ]
    exact hq

end ManuscriptAudit.IntegerGcdCyclicKernel
