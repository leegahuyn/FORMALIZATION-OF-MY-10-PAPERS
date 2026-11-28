import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! The actual printed single-filter moduli have trivial prime-power gcd,
and the printed additive perturbation has valuation exactly one. -/

namespace ManuscriptAudit.Paper4SingleFilterProfile

private theorem residue_not_dvd {p A : ℕ} (hA : 1 < A) (hAp : A < p) :
    ¬ (p : ℤ) ∣ (A : ℤ) - 1 := by
  have hCast : (((A - 1 : ℕ) : ℤ)) = (A : ℤ) - 1 :=
    Int.ofNat_sub (Nat.one_le_of_lt hA)
  intro h
  rw [← hCast] at h
  have hNat : p ∣ A - 1 := by
    simpa using Int.ofNat_dvd_right.mp h
  have hPos : 0 < A - 1 := Nat.sub_pos_of_lt hA
  have hLe : p ≤ A - 1 := Nat.le_of_dvd hPos hNat
  omega

/-- Neither sign in the actual printed arithmetic profile is divisible by p. -/
theorem modulus_not_dvd {p A : ℕ} (hA : 1 < A) (hAp : A < p)
    (y e : ℤ) (he : e = 1 ∨ e = -1) :
    ¬ (p : ℤ) ∣ (p : ℤ) * y + e * ((A : ℤ) - 1) := by
  intro h
  have hPy : (p : ℤ) ∣ (p : ℤ) * y := ⟨y, rfl⟩
  have hDiv : (p : ℤ) ∣ e * ((A : ℤ) - 1) := by
    convert Int.dvd_sub h hPy using 1 <;> ring
  apply residue_not_dvd hA hAp
  rcases he with rfl | rfl
  · simpa only [one_mul] using hDiv
  · simpa only [neg_one_mul, dvd_neg] using hDiv

/-- The scan's coprimality is an identity for every positive power of p,
throughout the printed range of A and for either sign and every y. -/
theorem gcd_prime_power_eq_one {p A m : ℕ} (hp : p.Prime) (hA : 1 < A) (hAp : A < p)
    (y e : ℤ) (he : e = 1 ∨ e = -1)
    (hm : (m : ℤ) = (p : ℤ) * y + e * ((A : ℤ) - 1)) (k : ℕ) :
    m.gcd (p ^ k) = 1 := by
  have hNot : ¬ p ∣ m := by
    intro h
    have hInt : (p : ℤ) ∣ (m : ℤ) := Int.ofNat_dvd_right.mpr (by simpa using h)
    rw [hm] at hInt
    exact modulus_not_dvd hA hAp y e he hInt
  exact (hp.coprime_pow_of_not_dvd hNot).gcd_eq_one

/-- The exact p-adic valuation of the literal additive perturbation. -/
theorem perturbation_valuation (p A : ℕ) [Fact p.Prime] :
    padicValNat p ((A ^ p + p) - A ^ p) = 1 := by
  rw [Nat.add_sub_cancel_left]
  exact padicValNat_self

end ManuscriptAudit.Paper4SingleFilterProfile

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4SingleFilterProfile.modulus_not_dvd,
      ``ManuscriptAudit.Paper4SingleFilterProfile.gcd_prime_power_eq_one,
      ``ManuscriptAudit.Paper4SingleFilterProfile.perturbation_valuation] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
