import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity

/-! Choosing exact prescribed odd-prime valuations in a sequence of power differences. -/

namespace ManuscriptAudit.FrobeniusOrderValuations

/-- Every sufficiently high valuation occurs exactly in x^k−1 for some positive k. -/
theorem eventually_exists_exact_factor (l x : ℕ) [Fact l.Prime] (hOdd : Odd l)
    (hx : 1 < x) (hCoprime : ¬l ∣ x) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ k d : ℕ, 0 < k ∧ x ^ k - 1 = l ^ n * d ∧ ¬l ∣ d := by
  have hl : l.Prime := Fact.out
  let s := l - 1
  have hs : 0 < s := Nat.sub_pos_of_lt hl.one_lt
  let b := x ^ s
  have hb : 1 < b := by
    simpa only [b, one_pow] using Nat.pow_lt_pow_left hx hs.ne'
  have hbDvd : l ∣ b - 1 := (Nat.dvd_iff_mod_eq_zero).mpr
    (Nat.pow_card_sub_one_sub_one_mod_card (p := l) (m := x) hl
      ((hl.coprime_iff_not_dvd).mpr hCoprime))
  have hbCoprime : ¬l ∣ b := fun h => hCoprime (hl.dvd_of_dvd_pow h)
  let N := padicValNat l (b - 1)
  refine ⟨N, fun n hn => ?_⟩
  let a := l ^ (n - N)
  let k := s * a
  have ha : 0 < a := pow_pos hl.pos _
  have hk : 0 < k := Nat.mul_pos hs ha
  have hval : padicValNat l (x ^ k - 1) = n := by
    change padicValNat l (x ^ (s * a) - 1) = _
    rw [pow_mul]
    change padicValNat l (b ^ a - 1) = _
    have h := padicValNat.pow_sub_pow (p := l) hOdd hb hbDvd hbCoprime ha.ne'
    simp only [one_pow] at h
    rw [h]
    change N + padicValNat l (l ^ (n - N)) = n
    rw [padicValNat.prime_pow]
    omega
  have hPos : 1 < x ^ k := by
    simpa only [one_pow] using Nat.pow_lt_pow_left hx hk.ne'
  have hy : x ^ k - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hPos
  have hDvd : l ^ n ∣ x ^ k - 1 := (padicValNat_dvd_iff_le hy).mpr hval.ge
  obtain ⟨d, hd⟩ := hDvd
  refine ⟨k, d, hk, hd, ?_⟩
  rintro ⟨e, he⟩
  have hBig : l ^ (n + 1) ∣ x ^ k - 1 := ⟨e, by rw [hd, he, pow_succ, mul_assoc]⟩
  have hle := (padicValNat_dvd_iff_le hy).mp hBig
  omega

end ManuscriptAudit.FrobeniusOrderValuations

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FrobeniusOrderValuations.eventually_exists_exact_factor
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
