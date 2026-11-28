import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-! The two stationary branches at odd prime powers and exact nilpotent inversion formulas. -/

namespace ManuscriptAudit.Paper8PrimePowerStationaryPhase

private theorem prime_pow_dvd_sub_or_add {p r x : ℕ} (hPrime : p.Prime) (hp : p ≠ 2)
    (hx : 0 < x) (hD : p ^ r ∣ (x - 1) * (x + 1)) :
    p ^ r ∣ x - 1 ∨ p ^ r ∣ x + 1 := by
  by_cases hL : p ∣ x - 1
  · have hR : ¬ p ∣ x + 1 := fun hR => by
      have hTwo := Nat.dvd_sub hR hL
      rw [show x + 1 - (x - 1) = 2 by omega] at hTwo
      exact hp ((Nat.prime_two.dvd_iff_eq hPrime.ne_one).1 hTwo).symm
    have hCop : (p ^ r).Coprime (x + 1) := (hPrime.coprime_iff_not_dvd.2 hR).pow_left r
    exact Or.inl (hCop.dvd_of_dvd_mul_right hD)
  · have hCop : (p ^ r).Coprime (x - 1) := (hPrime.coprime_iff_not_dvd.2 hL).pow_left r
    exact Or.inr (hCop.dvd_of_dvd_mul_left hD)

theorem prime_pow_sq_eq_one_iff {p r : ℕ} (hPrime : p.Prime) (hp : p ≠ 2)
    (u : ZMod (p ^ r)) : u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by
  let k := p ^ r
  have hk : 0 < k := pow_pos hPrime.pos _
  letI : NeZero k := ⟨hk.ne'⟩
  change (u : ZMod k) ^ 2 = 1 ↔ u = 1 ∨ u = -1
  constructor
  · intro h
    let x := u.val + k
    have hx : 0 < x := by unfold x; omega
    have hX : (x : ZMod k) = u := by unfold x; rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    have hD : k ∣ (x - 1) * (x + 1) := by
      apply (ZMod.natCast_eq_zero_iff _ k).1
      rw [Nat.cast_mul, Nat.cast_sub hx, Nat.cast_add, Nat.cast_one, hX,
        show (u - 1) * (u + 1) = u ^ 2 - 1 by ring, h, sub_self]
    rcases prime_pow_dvd_sub_or_add hPrime hp hx hD with hL | hR
    · left
      have he := (ZMod.natCast_eq_zero_iff (x - 1) k).2 hL
      rw [Nat.cast_sub hx, Nat.cast_one, hX] at he
      exact sub_eq_zero.mp he
    · right
      have he := (ZMod.natCast_eq_zero_iff (x + 1) k).2 hR
      rw [Nat.cast_add, Nat.cast_one, hX] at he
      linear_combination he
  · rintro (rfl | rfl) <;> ring

theorem linear_nilpotent_inverse {R : Type*} [CommRing R] {x y t : R}
    (hxy : x * y = 1) (ht : t ^ 2 = 0) :
    (x + t) * (y - y ^ 2 * t) = 1 := by
  linear_combination (1 - y * t) * hxy - y ^ 2 * ht

theorem quadratic_nilpotent_inverse {R : Type*} [CommRing R] {e t : R}
    (he : e ^ 2 = 1) (ht : t ^ 3 = 0) :
    (e + t) * (e - t + e * t ^ 2) = 1 := by
  linear_combination (1 + t ^ 2) * he + e * ht

theorem zmod_power_shift_nilpotent {p r n e : ℕ} (h : e ≤ r * n) (t : ZMod (p ^ e)) :
    (((p ^ r : ℕ) : ZMod (p ^ e)) * t) ^ n = 0 := by
  rw [mul_pow, ← Nat.cast_pow, ← pow_mul]
  rw [(ZMod.natCast_eq_zero_iff (p ^ (r * n)) (p ^ e)).2 (pow_dvd_pow _ h), zero_mul]

end ManuscriptAudit.Paper8PrimePowerStationaryPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8PrimePowerStationaryPhase.prime_pow_sq_eq_one_iff,
      ``ManuscriptAudit.Paper8PrimePowerStationaryPhase.quadratic_nilpotent_inverse,
      ``ManuscriptAudit.Paper8PrimePowerStationaryPhase.zmod_power_shift_nilpotent] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
