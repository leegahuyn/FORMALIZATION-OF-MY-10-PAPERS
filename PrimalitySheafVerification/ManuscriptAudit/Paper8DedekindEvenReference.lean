import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindEvenCRT
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindUnitFactor
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindTwoPrimaryBound

/-! Exact factorization of the actual even Dedekind coefficient when three does not divide the modulus. -/

namespace ManuscriptAudit.Paper8DedekindEvenReference

open Paper8DedekindEvenCRT Paper8DedekindUnitFactor Paper8DedekindTwoPrimaryData
open Paper8DedekindTwoPrimaryBound Paper8OddCrossJacobiSum Paper8ZModAdditiveCRT
open Paper8DedekindZeroReference Paper8KloostermanProductPhase

noncomputable section

theorem referenceZeroSum_even_factor {k e n : ℕ} [NeZero k] [NeZero n]
    (hk : k % 2 = 0) (hn : n % 2 = 1) (hK : k = 2 ^ e * n)
    (h3 : ¬ (3 : ℕ) ∣ k) (hCRT : (8 * 2 ^ e).Coprime n)
    (U V u v : ℤ)
    (hRemove : 3 * U + (8 * (k : ℤ)) * V = 1)
    (hBez : u * (n : ℤ) + v * ((8 * 2 ^ e : ℕ) : ℤ) = 1) :
    letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
    let R := 8 * 2 ^ e
    let d := u * U
    let c := v * U
    referenceZeroSum k =
      (8 : ℂ)⁻¹ * ZMod.stdAddChar (-(2 : ZMod R) * (k : ZMod R) * (d : ZMod R)) *
        twoPrimaryUnitSum (dvd_mul_right 8 (2 ^ e)) e n
          ((d : ZMod R) * (1 - (k : ZMod R))) ((d : ZMod R) * ((k : ZMod R) ^ 2 + 1)) *
        twistedSymmetricUnitSum (jacobiUnitWeight n) (c : ZMod n) := by
  let R := 8 * 2 ^ e
  let d := u * U
  let c := v * U
  letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  letI : NeZero R := ⟨mul_ne_zero (by decide) (NeZero.ne _)⟩
  let hd8 : 8 ∣ R := dvd_mul_right 8 (2 ^ e)
  let red8 := ZMod.castHom hd8 (ZMod 8)
  let A : ZMod R := (d : ZMod R) * (1 - (k : ZMod R))
  let B : ZMod R := (d : ZMod R) * ((k : ZMod R) ^ 2 + 1)
  let E := ZMod.stdAddChar (-(2 : ZMod R) * (k : ZMod R) * (d : ZMod R))
  let F (x : (ZMod R)ˣ) := twoPrimaryCharacter e n (red8 (x : ZMod R)) * kloostermanPhase A B (x : ZMod R)
  let G (y : (ZMod n)ˣ) := jacobiUnitWeight n y *
    ZMod.stdAddChar ((c : ZMod n) * ((y : ZMod n) + ((y⁻¹ : (ZMod n)ˣ) : ZMod n)))
  have hRM : R * n = 8 * k := by unfold R; rw [hK, mul_assoc]
  have hd : k ∣ R * n := ⟨8, hRM.trans (mul_comm _ _)⟩
  have hk2 : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk
  have hBoth (s : ℕ) (hs : s.Coprime k) : s.Coprime 8 :=
    (Nat.Coprime.of_dvd_right hk2 hs).pow_right 3
  let redK := ZMod.castHom hd (ZMod k)
  let eqv := unitsChineseRemainder hCRT
  have hTerm (x : (ZMod (R * n))ˣ) :
      referenceDedekindEntry k (redK (x : ZMod (R * n))) = E * (F (eqv x).1 * G (eqv x).2) := by
    let h := (x : ZMod (R * n)).val
    let X := (eqv x).1
    let Y := (eqv x).2
    have hRep : (h : ZMod (R * n)) = x := ZMod.natCast_zmod_val _
    have hhK : h.Coprime k := Nat.Coprime.of_dvd_right hd (ZMod.val_coe_unit_coprime x)
    have hh2 : h.Coprime 2 := Nat.Coprime.of_dvd_right hk2 hhK
    have hhO : h % 2 = 1 := by
      have hz : h % 2 ≠ 0 := fun h0 => (Nat.prime_two.coprime_iff_not_dvd.1 hh2.symm) (Nat.dvd_of_mod_eq_zero h0)
      omega
    have hRedK : (h : ZMod k) = redK (x : ZMod (R * n)) := by
      rw [← hRep, map_natCast]
    have hPair : (ZMod.chineseRemainder hCRT (h : ZMod (R * n))) = ((X : ZMod R), (Y : ZMod n)) := by
      rw [hRep] <;> rfl
    rw [map_natCast (ZMod.chineseRemainder hCRT)] at hPair
    have hX : (h : ZMod R) = X := congrArg Prod.fst hPair
    have hY : (h : ZMod n) = Y := congrArg Prod.snd hPair
    let a : ℤ := ((X⁻¹ : (ZMod R)ˣ) : ZMod R).val
    let b : ℤ := ((Y⁻¹ : (ZMod n)ˣ) : ZMod n).val
    have ha : (a : ZMod R) = ((X⁻¹ : (ZMod R)ˣ) : ZMod R) := by
      dsimp only [a]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hb : (b : ZMod n) = ((Y⁻¹ : (ZMod n)ˣ) : ZMod n) := by
      dsimp only [b]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hInvR : (h : ZMod R) * (a : ZMod R) = 1 := by rw [hX, ha]; exact X.mul_inv
    have hInvN : (h : ZMod n) * (b : ZMod n) = 1 := by rw [hY, hb]; exact Y.mul_inv
    have hχR : twoPrimaryCharacter e n (red8 (X : ZMod R)) =
        (ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e := by
      rw [← hX, map_natCast, twoPrimaryCharacter_natCast]
    have hχN : (jacobiSym (h : ℤ) n : ℂ) = jacobiUnitWeight n Y := by
      have hZ : ((h : ℤ) : ZMod n) = (((Y : ZMod n).val : ℤ) : ZMod n) := by
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val, hY]
      exact congrArg (fun j : ℤ => (j : ℂ)) (jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ n).1 hZ))
    have hPhase : ZMod.stdAddChar ((d : ZMod R) * ((1 - (k : ZMod R)) * (h : ZMod R) +
          ((k : ZMod R) ^ 2 + 1) * (a : ZMod R))) = kloostermanPhase A B (X : ZMod R) := by
      unfold kloostermanPhase A B
      rw [hX, ha, ZMod.inv_coe_unit]
      congr 1
      ring
    have hE := dedekind_even_crt_summand hhO hk hn hK hhK h3 hCRT U V u v a b hRemove hBez hInvR hInvN
    change Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((Paper8ContourResidueWeights.dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
        E * ((ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e) *
        ZMod.stdAddChar ((d : ZMod R) * ((1 - (k : ZMod R)) * (h : ZMod R) +
          ((k : ZMod R) ^ 2 + 1) * (a : ZMod R))) *
        (jacobiSym (h : ℤ) n : ℂ) *
        ZMod.stdAddChar ((c : ZMod n) * ((h : ZMod n) + (b : ZMod n))) at hE
    rw [referenceDedekindEntry_of_cast hRedK, hE, ← hχR, hPhase, hχN, hY, hb]
    change _ = E * (F X * G Y)
    unfold F G
    ring
  have hFactor := referenceZeroSum_factor_coprime hRM hd hCRT hBoth E F G hTerm
  change referenceZeroSum k = (8 : ℂ)⁻¹ * E * twoPrimaryUnitSum hd8 e n A B *
    twistedSymmetricUnitSum (jacobiUnitWeight n) (c : ZMod n)
  simpa only [Nat.cast_ofNat, twoPrimaryUnitSum, twistedSymmetricUnitSum, F, G] using hFactor

end
end ManuscriptAudit.Paper8DedekindEvenReference

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindEvenReference.referenceZeroSum_even_factor
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
