import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicUnitModFourFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CubicNoncubeTraceRatio
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticTwistRotation
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSexticTwists
import PrimalitySheafVerification.ManuscriptAudit.TorsionSignedTraceConjugacy

/-! Native mod-four arithmetic trace for a noncube split twist when the field size is three modulo four. -/

namespace ManuscriptAudit.CubicSplitNoncubeModFourTrace

open Module FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace CubicSplitTwoPowerFrobenius CubicFrobeniusSexticTwists
open CubicPointScaling CubicSexticTwistRotation TorsionFrobeniusModule
open TorsionSignedTraceConjugacy

noncomputable section

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K L]

/-- The actual trace on four-torsion equals the signed projective count for the noncube
twist of every split centered cubic with field size three modulo four. -/
theorem native_trace_eq_count {A z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3) (hNc : ¬ ∃ x : K, x ^ 3 = A)
    (hq₄ : (Fintype.card K : ZMod 4) = 3) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
      (((Fintype.card K : ℤ) + 1 -
        (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ) : ℤ) : ZMod 4) := by
  let i := algebraMap K L
  let q := Fintype.card K
  let k := q / 6
  let v := A ^ k
  let ε := quadraticChar K A
  let w := i (parameter (1 : K) A k)
  let R := geometricRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz
  let S := levelRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz 2
  let f₁ := arithmeticPointFrobenius K L (1 : K)
  let fA := arithmeticPointFrobenius K L A
  have hchar : ringChar K ≠ 2 := by
    intro h
    exact h₂ ((ringChar.spec K 2).mpr (by simpa only [h] using (dvd_rfl : (2 : ℕ) ∣ 2)))
  have hOdd := FiniteField.odd_card_of_char_ne_two hchar
  have hzdiv : 3 ∣ Fintype.card K - 1 := by
    rw [hz.eq_orderOf]
    exact orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one z (hz.ne_zero (by decide)))
  have hq : Fintype.card K = 6 * k + 1 := by
    have hp : 0 < Fintype.card K := Fintype.card_pos
    dsimp only [k, q]
    omega
  have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ hA
  have hqMod : Fintype.card K % 4 = 3 :=
    (ZMod.natCast_eq_natCast_iff' (Fintype.card K) 3 4).mp hq₄
  obtain ⟨hvCube, hvNe, hvSign, hArith⟩ :=
    CubicNoncubeTraceRatio.noncube_ratio_trace L hA hz hNc hchar hΔ hq₄ hq
  have hCases : v ^ 2 = z ∨ v ^ 2 = z ^ 2 := by
    obtain ⟨j, hj, hjv⟩ := hz.eq_pow_of_pow_eq_one hvCube
    have hj₀ : j ≠ 0 := by
      intro h
      rw [h, pow_zero] at hjv
      exact hvNe hjv.symm
    have hj' : j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl
    · exact Or.inl (by simpa only [pow_one] using hjv.symm)
    · exact Or.inr hjv.symm
  have h₂L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero i).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero i).mpr h₃
  have h₁L : i (1 : K) ≠ 0 := (map_ne_zero i).mpr one_ne_zero
  have hAL : i A ≠ 0 := (map_ne_zero i).mpr hA
  have hΔ₁ := shortCubic_discriminant_ne_zero h₂L h₃L h₁L
  have hΔA := shortCubic_discriminant_ne_zero h₂L h₃L hAL
  have hzL := hz.map_of_injective i.injective
  have hε : ε = 1 ∨ ε = -1 := quadraticChar_dichotomy hA
  obtain ⟨hw, hW, e, he⟩ := exists_conjugacy K L (A := (1 : K)) (B := A)
    one_ne_zero hA hq hΔ₁ hΔA
  have hwv : w = i v := by simp [w, parameter, v]
  have hwSig : w ^ 3 = (ε : L) := by rw [hwv, ← map_pow, hvSign, map_intCast]
  have trTransfer (r : AddMonoid.End (GeometricPoints K L (1 : K)))
      (hs : scale hw hW hΔ₁ = ε • r) :
      LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
        (ε : ZMod 4) * LinearMap.trace (ZMod 4) (Level K L (1 : K) 2)
          (mapLinear 4 r * levelFrobenius K L (1 : K) 2) := by
    apply trace_eq_of_signed_conjugacy (G := GeometricPoints K L (1 : K))
      (H := GeometricPoints K L A) 4 e f₁ r fA ε
    intro P
    have h : fA (e P) = e (scale hw hW hΔ₁ (f₁ P)) := he P
    rw [hs] at h
    rcases hε with h1 | h1
    · simp only [h1, one_zsmul] at h ⊢
      exact h
    · rw [h1, neg_one_zsmul] at h ⊢
      change fA (e P) = e (-r (f₁ P)) at h
      exact h
  have hRef := CubicUnitModFourFrobenius.rotated_trace K L h₂ h₃ hz hqMod
  rcases hCases with h | h
  · have hSq : w ^ 2 = i z := by rw [hwv, ← map_pow, h]
    have hSc : scale hw hW hΔ₁ = ε • R :=
      scale_eq_signed_rotate hΔ₁ hw hW hzL.pow_eq_one hSq ε hε hwSig
    have hTr := trTransfer R hSc
    change _ = (ε : ZMod 4) * LinearMap.trace (ZMod 4) _
      (S * levelFrobenius K L (1 : K) 2) at hTr
    rw [hRef.1] at hTr
    rw [h] at hArith
    exact hTr.trans hArith.symm
  · have hSq : w ^ 2 = (i z) ^ 2 := by rw [hwv, ← map_pow, h, map_pow]
    have hc : ((i z) ^ 2) ^ 3 = 1 := by
      rw [pow_right_comm (i z) 2 3, hzL.pow_eq_one, one_pow]
    have hSc : scale hw hW hΔ₁ = ε • R ^ 2 := by
      have heq := scale_eq_signed_rotate hΔ₁ hw hW hc hSq ε hε hwSig
      rw [rotate_square_eq hΔ₁ hzL.pow_eq_one hc] at heq
      change scale hw hW hΔ₁ = ε • R.comp R
      exact heq
    have hTr := trTransfer (R ^ 2) hSc
    have hSqLin : mapLinear 4 (R ^ (2 : ℕ)) = S ^ 2 :=
      mapLinear_sq (G := GeometricPoints K L (1 : K)) 4 R
    rw [hSqLin] at hTr
    change _ = (ε : ZMod 4) * LinearMap.trace (ZMod 4) _
      (S ^ 2 * levelFrobenius K L (1 : K) 2) at hTr
    rw [hRef.2] at hTr
    rw [h, CubicHalfFrobeniusSigns.difference_signs K hz hqMod, Int.cast_neg] at hArith
    exact hTr.trans hArith.symm

end
end ManuscriptAudit.CubicSplitNoncubeModFourTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitNoncubeModFourTrace.native_trace_eq_count
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
