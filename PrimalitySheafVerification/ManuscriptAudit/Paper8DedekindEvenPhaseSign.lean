import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindEvenPhase

/-! Remove the inverse from the quadratic sign term of the native two-primary phase. -/

namespace ManuscriptAudit.Paper8DedekindEvenPhaseSign

open Paper8DedekindEvenPhase Paper8DedekindKloostermanCongruence

private theorem odd_nat_cast_equals_chiFour {h : ℕ} (hh : h % 2 = 1) :
    (h : ZMod 4) = (ZMod.χ₄ h : ZMod 4) := by
  have hCases : h % 4 = 1 ∨ h % 4 = 3 := by omega
  rcases hCases with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, Int.cast_one]
    change (h : ZMod 4) = ((1 : ℕ) : ZMod 4)
    exact (ZMod.natCast_eq_natCast_iff' h 1 4).2 (by simpa using h1)
  · rw [ZMod.χ₄_nat_three_mod_four h3]
    have hC : (h : ZMod 4) = ((3 : ℕ) : ZMod 4) :=
      (ZMod.natCast_eq_natCast_iff' h 3 4).2 (by simpa using h3)
    rw [hC]
    decide

private theorem odd_nat_cast_sq_four {h : ℕ} (hh : h % 2 = 1) :
    (h : ZMod 4) ^ 2 = 1 := by
  have hCases : h % 4 = 1 ∨ h % 4 = 3 := by omega
  rcases hCases with h1 | h3
  · rw [odd_nat_cast_equals_chiFour hh, ZMod.χ₄_nat_one_mod_four h1, Int.cast_one, one_pow]
  · rw [odd_nat_cast_equals_chiFour hh, ZMod.χ₄_nat_three_mod_four h3, Int.cast_neg, Int.cast_one, neg_sq, one_pow]

theorem phase_even_numerator_two_part_signed {h k t : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 0)
    (hk0 : 0 < k) (hC : h.Coprime k) (ht : t ∣ k) (a : ℤ)
    (ha : (h : ZMod (8 * t)) * (a : ZMod (8 * t)) = 1) :
    (dedekindPhaseNumerator h k : ZMod (8 * t)) =
      (1 - (k : ZMod (8 * t))) * (h : ZMod (8 * t)) +
        ((k : ZMod (8 * t)) ^ 2 + 1) * (a : ZMod (8 * t)) -
        2 * (k : ZMod (8 * t)) * (jacobiSym (-(k : ℤ)) h : ZMod (8 * t)) := by
  let M := 8 * t
  have hD : 4 ∣ M := ⟨2 * t, by unfold M; ring⟩
  let f := ZMod.castHom hD (ZMod 4)
  have hInv4 : (h : ZMod 4) * (a : ZMod 4) = 1 := by
    have h := congrArg f ha
    simpa only [map_mul, map_one, map_intCast, map_natCast] using h
  have hA : (a : ZMod 4) = (h : ZMod 4) := by
    calc
      _ = (h : ZMod 4) ^ 2 * (a : ZMod 4) := by rw [odd_nat_cast_sq_four hh, one_mul]
      _ = (h : ZMod 4) * ((h : ZMod 4) * (a : ZMod 4)) := by rw [pow_two, mul_assoc]
      _ = _ := by rw [hInv4, mul_one]
  let J := jacobiSym (k : ℤ) h
  let Jn := jacobiSym (-(k : ℤ)) h
  have hSign : (a : ZMod 4) * (J : ZMod 4) = (Jn : ZMod 4) := by
    unfold J Jn
    rw [hA, odd_nat_cast_equals_chiFour hh, jacobiSym.neg _ (Nat.odd_iff.mpr hh), Int.cast_mul]
  have h4 : (4 : ℤ) ∣ a * J - Jn := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1
    push_cast
    rw [hSign, sub_self]
  have hMD : (M : ℤ) ∣ (2 * (k : ℤ)) * (a * J - Jn) := by
    obtain ⟨q, hq⟩ := ht
    obtain ⟨r, hr⟩ := h4
    have hz := congrArg (fun x : ℕ => (x : ℤ)) hq
    push_cast at hz
    refine ⟨q * r, ?_⟩
    rw [hz, hr]
    unfold M
    push_cast
    ring
  have hZ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).2 hMD
  push_cast at hZ
  have hE : (2 : ZMod M) * (k : ZMod M) * (a : ZMod M) * (J : ZMod M) =
      (2 : ZMod M) * (k : ZMod M) * (Jn : ZMod M) := by
    linear_combination hZ
  rw [phase_even_numerator_two_part hh hk hk0 hC ht a ha, hE]

end ManuscriptAudit.Paper8DedekindEvenPhaseSign

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindEvenPhaseSign.phase_even_numerator_two_part_signed
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
