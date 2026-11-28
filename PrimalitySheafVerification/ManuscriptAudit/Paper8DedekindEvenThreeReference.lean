import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindEvenThreeCRT
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossThreeSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindUnitFactor
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindTwoPrimaryBound

/-! Exact factorization of the actual even Dedekind coefficient when three divides the modulus. -/

namespace ManuscriptAudit.Paper8DedekindEvenThreeReference

open Paper8DedekindEvenThreeCRT Paper8OddCrossThreeSum Paper8ProductStationaryPhase Paper8DedekindUnitFactor Paper8DedekindTwoPrimaryData
open Paper8DedekindTwoPrimaryBound Paper8OddCrossJacobiSum Paper8ZModAdditiveCRT
open Paper8DedekindZeroReference Paper8KloostermanProductPhase

noncomputable section

theorem referenceZeroSum_even_three_factor {k e n : ℕ} [NeZero k] [NeZero n]
    (hk : k % 2 = 0) (hn : n % 2 = 1) (hK : k = 2 ^ e * n)
    (h3 : (3 : ℕ) ∣ k) (hCRT : (8 * 2 ^ e).Coprime (3 * n))
    (u v : ℤ) (hBez : u * ((3 * n : ℕ) : ℤ) + v * ((8 * 2 ^ e : ℕ) : ℤ) = 1) :
    letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
    let R := 8 * 2 ^ e
    let S := 3 * n
    referenceZeroSum k =
      (24 : ℂ)⁻¹ * ZMod.stdAddChar (-(2 : ZMod R) * (k : ZMod R) * (u : ZMod R)) *
        twoPrimaryUnitSum (dvd_mul_right 8 (2 ^ e)) e n
          ((u : ZMod R) * (1 - (k : ZMod R))) ((u : ZMod R) * ((k : ZMod R) ^ 2 + 1)) *
        twistedSymmetricUnitSum (jacobiLiftWeight n) (v : ZMod S) := by
  let R := 8 * 2 ^ e
  let S := 3 * n
  letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  letI : NeZero R := ⟨mul_ne_zero (by decide) (NeZero.ne _)⟩
  letI : NeZero S := ⟨mul_ne_zero (by decide) (NeZero.ne _)⟩
  let hd8 : 8 ∣ R := dvd_mul_right 8 (2 ^ e)
  let red8 := ZMod.castHom hd8 (ZMod 8)
  let A : ZMod R := (u : ZMod R) * (1 - (k : ZMod R))
  let B : ZMod R := (u : ZMod R) * ((k : ZMod R) ^ 2 + 1)
  let E := ZMod.stdAddChar (-(2 : ZMod R) * (k : ZMod R) * (u : ZMod R))
  let F (x : (ZMod R)ˣ) := twoPrimaryCharacter e n (red8 (x : ZMod R)) * kloostermanPhase A B (x : ZMod R)
  let G (y : (ZMod S)ˣ) := jacobiLiftWeight n y *
    ZMod.stdAddChar ((v : ZMod S) * ((y : ZMod S) + ((y⁻¹ : (ZMod S)ˣ) : ZMod S)))
  have hRM : R * S = 24 * k := by unfold R S; rw [hK]; ring
  have hd : k ∣ R * S := ⟨24, hRM.trans (mul_comm _ _)⟩
  have hk2 : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk
  have hBoth (s : ℕ) (hs : s.Coprime k) : s.Coprime 24 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by decide, Nat.coprime_mul_iff_right]
    exact ⟨(Nat.Coprime.of_dvd_right hk2 hs).pow_right 3, Nat.Coprime.of_dvd_right h3 hs⟩
  let redK := ZMod.castHom hd (ZMod k)
  let eqv := unitsChineseRemainder hCRT
  have hTerm (x : (ZMod (R * S))ˣ) :
      referenceDedekindEntry k (redK (x : ZMod (R * S))) = E * (F (eqv x).1 * G (eqv x).2) := by
    let h := (x : ZMod (R * S)).val
    let X := (eqv x).1
    let Y := (eqv x).2
    have hRep : (h : ZMod (R * S)) = x := ZMod.natCast_zmod_val _
    have hhK : h.Coprime k := Nat.Coprime.of_dvd_right hd (ZMod.val_coe_unit_coprime x)
    have hh2 : h.Coprime 2 := Nat.Coprime.of_dvd_right hk2 hhK
    have hhO : h % 2 = 1 := by
      have hz : h % 2 ≠ 0 := fun h0 => (Nat.prime_two.coprime_iff_not_dvd.1 hh2.symm) (Nat.dvd_of_mod_eq_zero h0)
      omega
    have hRedK : (h : ZMod k) = redK (x : ZMod (R * S)) := by
      rw [← hRep, map_natCast]
    have hPair : (ZMod.chineseRemainder hCRT (h : ZMod (R * S))) = ((X : ZMod R), (Y : ZMod S)) := by
      rw [hRep] <;> rfl
    rw [map_natCast (ZMod.chineseRemainder hCRT)] at hPair
    have hX : (h : ZMod R) = X := congrArg Prod.fst hPair
    have hY : (h : ZMod S) = Y := congrArg Prod.snd hPair
    let a : ℤ := ((X⁻¹ : (ZMod R)ˣ) : ZMod R).val
    let b : ℤ := ((Y⁻¹ : (ZMod S)ˣ) : ZMod S).val
    have ha : (a : ZMod R) = ((X⁻¹ : (ZMod R)ˣ) : ZMod R) := by
      dsimp only [a]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hb : (b : ZMod S) = ((Y⁻¹ : (ZMod S)ˣ) : ZMod S) := by
      dsimp only [b]
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hInvR : (h : ZMod R) * (a : ZMod R) = 1 := by rw [hX, ha]; exact X.mul_inv
    have hInvN : (h : ZMod S) * (b : ZMod S) = 1 := by rw [hY, hb]; exact Y.mul_inv
    have hχR : twoPrimaryCharacter e n (red8 (X : ZMod R)) =
        (ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e := by
      rw [← hX, map_natCast, twoPrimaryCharacter_natCast]
    have hχN : (jacobiSym (h : ℤ) n : ℂ) = jacobiLiftWeight n Y := by
      let z := @reduceLowDigit 3 n (Y : ZMod S)
      have hZ' : (h : ZMod n) = z := by
        change (h : ZMod n) = reduceLowDigit (Y : ZMod S)
        rw [← hY, map_natCast]
      have hz : ((h : ℤ) : ZMod n) = ((z.val : ℤ) : ZMod n) := by
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val, hZ']
      exact congrArg (fun j : ℤ => (j : ℂ)) (jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ n).1 hz))
    have hPhase : ZMod.stdAddChar ((u : ZMod R) * ((1 - (k : ZMod R)) * (h : ZMod R) +
          ((k : ZMod R) ^ 2 + 1) * (a : ZMod R))) = kloostermanPhase A B (X : ZMod R) := by
      unfold kloostermanPhase A B
      rw [hX, ha, ZMod.inv_coe_unit]
      congr 1
      ring
    have hE := dedekind_even_three_crt_summand hhO hk hn hK hhK h3 hCRT u v a b hBez hInvR hInvN
    change Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((Paper8ContourResidueWeights.dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
        E * ((ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e) *
        ZMod.stdAddChar ((u : ZMod R) * ((1 - (k : ZMod R)) * (h : ZMod R) +
          ((k : ZMod R) ^ 2 + 1) * (a : ZMod R))) *
        (jacobiSym (h : ℤ) n : ℂ) *
        ZMod.stdAddChar ((v : ZMod S) * ((h : ZMod S) + (b : ZMod S))) at hE
    rw [referenceDedekindEntry_of_cast hRedK, hE, ← hχR, hPhase, hχN, hY, hb]
    change _ = E * (F X * G Y)
    unfold F G
    ring
  have hFactor := referenceZeroSum_factor_coprime hRM hd hCRT hBoth E F G hTerm
  change referenceZeroSum k = (24 : ℂ)⁻¹ * E * twoPrimaryUnitSum hd8 e n A B *
    twistedSymmetricUnitSum (jacobiLiftWeight n) (v : ZMod S)
  simpa only [Nat.cast_ofNat, twoPrimaryUnitSum, twistedSymmetricUnitSum, F, G] using hFactor

end
end ManuscriptAudit.Paper8DedekindEvenThreeReference

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindEvenThreeReference.referenceZeroSum_even_three_factor
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
