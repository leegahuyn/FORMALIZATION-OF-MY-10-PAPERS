import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindAdditiveReduction
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindEvenAdditive
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindEvenCharacter
import PrimalitySheafVerification.ManuscriptAudit.Paper8ZModAdditiveCRT

/-! Exact even Dedekind CRT phase, including denominators divisible by three. -/

namespace ManuscriptAudit.Paper8DedekindEvenThreeCRT

open Paper8ContourResidueWeights Paper8DedekindKloostermanCongruence
open Paper8DedekindEvenAdditive Paper8DedekindEvenCharacter Paper8ZModAdditiveCRT

noncomputable section

theorem phase_numerator_congr_divisor_three_mul {h k m : ℕ} (hk : 0 < k) (hC : h.Coprime k)
    (h3 : 3 ∣ k) (hd : m ∣ 3 * k) (a : ℤ) (ha : (h : ZMod m) * (a : ZMod m) = 1) :
    (dedekindPhaseNumerator h k : ZMod m) = (h : ZMod m) + (a : ZMod m) := by
  let N := dedekindPhaseNumerator h k
  have hD : (m : ℤ) ∣ (h : ℤ) * N - (1 + (h : ℤ) ^ 2) := by
    have hDiv := Int.natCast_dvd_natCast.2 hd
    push_cast at hDiv
    exact hDiv.trans ((dedekind_phase_numerator_spec hk hC).2.2.1 h3)
  have hZ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).2 hD
  push_cast at hZ
  have hN := sub_eq_zero.mp hZ
  calc
    _ = (a : ZMod m) * ((h : ZMod m) * (N : ZMod m)) := by
      rw [← mul_assoc, mul_comm (a : ZMod m), ha, one_mul]
    _ = _ := by
      rw [hN, mul_add, mul_one, pow_two, ← mul_assoc, mul_comm (a : ZMod m), ha, one_mul]
      exact add_comm _ _

private theorem dedekind_phase_as_stdAddChar {h k M : ℕ} [NeZero k] [NeZero M]
    (hM : M = 24 * k) (hC : h.Coprime k) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      ZMod.stdAddChar (dedekindPhaseNumerator h k : ZMod M) := by
  have hk := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hN := congrArg (fun x : ℚ => (x : ℂ)) (dedekind_phase_numerator_spec hk hC).1
  push_cast at hN
  have hMC := congrArg (fun x : ℕ => (x : ℂ)) hM
  push_cast at hMC
  rw [ZMod.stdAddChar_coe, hN, hMC]
  congr 1
  push_cast
  field_simp [hkC] <;> ring

theorem dedekind_even_three_crt_summand {h k e n : ℕ} [NeZero k] [NeZero n]
    (hh : h % 2 = 1) (hk : k % 2 = 0) (hn : n % 2 = 1) (hK : k = 2 ^ e * n)
    (hC : h.Coprime k) (h3 : (3 : ℕ) ∣ k) (hCRT : (8 * 2 ^ e).Coprime (3 * n))
    (u v a b : ℤ)
    (hBez : u * ((3 * n : ℕ) : ℤ) + v * ((8 * 2 ^ e : ℕ) : ℤ) = 1)
    (ha : (h : ZMod (8 * 2 ^ e)) * (a : ZMod (8 * 2 ^ e)) = 1)
    (hb : (h : ZMod (3 * n)) * (b : ZMod (3 * n)) = 1) :
    letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
    let R := 8 * 2 ^ e
    let S := 3 * n
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      ZMod.stdAddChar (-(2 : ZMod R) * (k : ZMod R) * (u : ZMod R)) *
        ((ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e) *
        ZMod.stdAddChar ((u : ZMod R) * ((1 - (k : ZMod R)) * (h : ZMod R) +
          ((k : ZMod R) ^ 2 + 1) * (a : ZMod R))) *
        (jacobiSym (h : ℤ) n : ℂ) *
        ZMod.stdAddChar ((v : ZMod S) * ((h : ZMod S) + (b : ZMod S))) := by
  let R := 8 * 2 ^ e
  let S := 3 * n
  let N := dedekindPhaseNumerator h k
  letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  letI : NeZero R := ⟨mul_ne_zero (by decide : (8 : ℕ) ≠ 0) (NeZero.ne _)⟩
  letI : NeZero S := ⟨mul_ne_zero (by decide : (3 : ℕ) ≠ 0) (NeZero.ne _)⟩
  have hR0 : (R : ZMod 2) = 0 := by
    unfold R
    rw [Nat.cast_mul, show ((8 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
  have hS1 : (S : ZMod 2) = 1 := by
    have hN1 : (n : ZMod 2) = 1 := by
      change (n : ZMod 2) = ((1 : ℕ) : ZMod 2)
      exact (ZMod.natCast_eq_natCast_iff' n 1 2).2 (by simpa using hn)
    unfold S
    rw [Nat.cast_mul, show ((3 : ℕ) : ZMod 2) = 1 by decide, hN1, mul_one]
  have hu : (2 : ℤ) ∣ u - 1 := by
    have h := congrArg (fun x : ℤ => (x : ZMod 2)) hBez
    change (((u * (S : ℤ) + v * (R : ℤ) : ℤ)) : ZMod 2) = (1 : ZMod 2) at h
    push_cast at h
    have h1 : (u : ZMod 2) = 1 := by simpa only [hS1, hR0, mul_one, mul_zero, add_zero] using h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1
    push_cast
    rw [h1, sub_self]
  have hM : R * S = 24 * k := by unfold R S; rw [hK]; ring
  have hSplit : Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      ZMod.stdAddChar ((u : ZMod R) * (N : ZMod R)) * ZMod.stdAddChar ((v : ZMod S) * (N : ZMod S)) := by
    rw [dedekind_phase_as_stdAddChar hM hC]
    have h := stdAddChar_chineseRemainder hCRT u v hBez (N : ZMod (R * S))
    rw [map_intCast (ZMod.chineseRemainder hCRT)] at h
    exact h
  have hTwo := stdAddChar_even_phase_factor hh hk (Nat.pos_of_ne_zero (NeZero.ne k)) hC hK hn a u hu ha
  have hd : S ∣ 3 * k := ⟨2 ^ e, by unfold S; rw [hK]; ring⟩
  have hOdd := phase_numerator_congr_divisor_three_mul (Nat.pos_of_ne_zero (NeZero.ne k)) hC h3 hd b hb
  have hJac : jacobiSym (-(k : ℤ)) h =
      (ZMod.χ₄ h) ^ (n / 2 + 1) * (ZMod.χ₈ h) ^ e * jacobiSym (h : ℤ) n := by
    rw [hK]
    exact jacobi_neg_two_part hh hn
  change _ = ZMod.stdAddChar (-(2 : ZMod R) * (k : ZMod R) * (u : ZMod R)) *
        ((ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e) *
        ZMod.stdAddChar ((u : ZMod R) * ((1 - (k : ZMod R)) * (h : ZMod R) +
          ((k : ZMod R) ^ 2 + 1) * (a : ZMod R))) *
        (jacobiSym (h : ℤ) n : ℂ) *
        ZMod.stdAddChar ((v : ZMod S) * ((h : ZMod S) + (b : ZMod S)))
  rw [hSplit, hTwo, hOdd, hJac]
  push_cast
  ring

end
end ManuscriptAudit.Paper8DedekindEvenThreeCRT

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindEvenThreeCRT.dedekind_even_three_crt_summand
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
