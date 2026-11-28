import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindAdditiveReduction
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindEvenAdditive
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindEvenCharacter
import PrimalitySheafVerification.ManuscriptAudit.Paper8ZModAdditiveCRT

/-! The actual even Dedekind summand separates into the coprime two-primary and odd phases. -/

namespace ManuscriptAudit.Paper8DedekindEvenCRT

open Paper8ContourResidueWeights Paper8DedekindKloostermanCongruence
open Paper8DedekindAdditiveReduction Paper8DedekindEvenAdditive Paper8DedekindEvenCharacter
open Paper8ZModAdditiveCRT

noncomputable section

private theorem stdAddChar_int_cast_modulus_eq {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (a : ℤ) :
    ZMod.stdAddChar (a : ZMod m) = ZMod.stdAddChar (a : ZMod n) := by
  subst n
  rfl

theorem dedekind_even_crt_summand {h k e n : ℕ} [NeZero k] [NeZero n]
    (hh : h % 2 = 1) (hk : k % 2 = 0) (hn : n % 2 = 1) (hK : k = 2 ^ e * n)
    (hC : h.Coprime k) (h3 : ¬ (3 : ℕ) ∣ k) (hCRT : (8 * 2 ^ e).Coprime n)
    (U V u v a b : ℤ)
    (hRemove : 3 * U + (8 * (k : ℤ)) * V = 1)
    (hBez : u * (n : ℤ) + v * ((8 * 2 ^ e : ℕ) : ℤ) = 1)
    (ha : (h : ZMod (8 * 2 ^ e)) * (a : ZMod (8 * 2 ^ e)) = 1)
    (hb : (h : ZMod n) * (b : ZMod n) = 1) :
    letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
    let R := 8 * 2 ^ e
    let d := u * U
    let c := v * U
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      ZMod.stdAddChar (-(2 : ZMod R) * (k : ZMod R) * (d : ZMod R)) *
        ((ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e) *
        ZMod.stdAddChar ((d : ZMod R) * ((1 - (k : ZMod R)) * (h : ZMod R) +
          ((k : ZMod R) ^ 2 + 1) * (a : ZMod R))) *
        (jacobiSym (h : ℤ) n : ℂ) *
        ZMod.stdAddChar ((c : ZMod n) * ((h : ZMod n) + (b : ZMod n))) := by
  let R := 8 * 2 ^ e
  let d := u * U
  let c := v * U
  let N := dedekindPhaseNumerator h k
  letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  letI : NeZero R := ⟨mul_ne_zero (by decide : (8 : ℕ) ≠ 0) (NeZero.ne _)⟩
  have hR0 : (R : ZMod 2) = 0 := by
    unfold R
    rw [Nat.cast_mul]
    have h8 : ((8 : ℕ) : ZMod 2) = 0 := by decide
    rw [h8, zero_mul]
  have hN1 : (n : ZMod 2) = 1 := by
    change (n : ZMod 2) = ((1 : ℕ) : ZMod 2)
    exact (ZMod.natCast_eq_natCast_iff' n 1 2).2 (by simpa using hn)
  have hU1 : (U : ZMod 2) = 1 := by
    have h := congrArg (fun x : ℤ => (x : ZMod 2)) hRemove
    push_cast at h
    simpa only [show (3 : ZMod 2) = 1 by decide, show (8 : ZMod 2) = 0 by decide,
      one_mul, zero_mul, add_zero] using h
  have hu1 : (u : ZMod 2) = 1 := by
    have h := congrArg (fun x : ℤ => (x : ZMod 2)) hBez
    change (((u * (n : ℤ) + v * (R : ℤ) : ℤ)) : ZMod 2) = (1 : ZMod 2) at h
    push_cast at h
    simpa only [hN1, hR0, mul_one, mul_zero, add_zero] using h
  have hd : (2 : ℤ) ∣ d - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1
    unfold d
    push_cast
    rw [hu1, hU1, mul_one, sub_self]
  have hM : 8 * k = R * n := by
    unfold R
    rw [hK, mul_assoc]
  have hSplit : Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      ZMod.stdAddChar ((d * N : ℤ) : ZMod R) * ZMod.stdAddChar ((c * N : ℤ) : ZMod n) := by
    rw [dedekind_phase_drop_three h3 hC U V hRemove, stdAddChar_int_cast_modulus_eq hM]
    have h := stdAddChar_chineseRemainder hCRT u v hBez ((U * N : ℤ) : ZMod (R * n))
    rw [map_intCast (ZMod.chineseRemainder hCRT)] at h
    change ZMod.stdAddChar ((U * N : ℤ) : ZMod (R * n)) =
      ZMod.stdAddChar ((u : ZMod R) * ((U * N : ℤ) : ZMod R)) *
      ZMod.stdAddChar ((v : ZMod n) * ((U * N : ℤ) : ZMod n)) at h
    simpa only [d, c, Int.cast_mul, mul_assoc] using h
  have hTwo := stdAddChar_even_phase_factor hh hk (Nat.pos_of_ne_zero (NeZero.ne k)) hC hK hn a d hd ha
  have hOdd := phase_numerator_congr_divisor (Nat.pos_of_ne_zero (NeZero.ne k)) hC
    (show n ∣ k from by rw [hK]; exact dvd_mul_left n (2 ^ e)) b hb
  have hJac : jacobiSym (-(k : ℤ)) h =
      (ZMod.χ₄ h) ^ (n / 2 + 1) * (ZMod.χ₈ h) ^ e * jacobiSym (h : ℤ) n := by
    rw [hK]
    exact jacobi_neg_two_part hh hn
  change _ = ZMod.stdAddChar (-(2 : ZMod R) * (k : ZMod R) * (d : ZMod R)) *
        ((ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e) *
        ZMod.stdAddChar ((d : ZMod R) * ((1 - (k : ZMod R)) * (h : ZMod R) +
          ((k : ZMod R) ^ 2 + 1) * (a : ZMod R))) *
        (jacobiSym (h : ℤ) n : ℂ) *
        ZMod.stdAddChar ((c : ZMod n) * ((h : ZMod n) + (b : ZMod n)))
  rw [hSplit, Int.cast_mul d N, Int.cast_mul c N, hTwo, hOdd, hJac]
  push_cast
  ring

end
end ManuscriptAudit.Paper8DedekindEvenCRT

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindEvenCRT.dedekind_even_crt_summand
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
