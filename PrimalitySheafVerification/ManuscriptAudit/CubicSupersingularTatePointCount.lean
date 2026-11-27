import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularArithmeticCounts
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularTwistTateFormula

/-! Equality of the genuine Tate trace and the literal signed point count. -/

namespace ManuscriptAudit.CubicSupersingularTatePointCount

open Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace PowerTateModule
open CubicSexticRotation CubicSupersingularTwistFrobenius CubicSupersingularArithmeticCounts
open CubicSupersingularTwistTateFormula

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E] [Algebra E L]

/-- For every nonzero twist over an even-degree base, the actual trace agrees with its point count. -/
theorem trace_det_eq_point_count (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    {m : ℕ} (hm : finrank (ZMod p) E = 2 * m) (hm₀ : 0 < m)
    {A : E} (hA : A ≠ 0) :
    let T := endMap l (arithmeticPointFrobenius E L A)
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A)) T =
      (Int.cast ((Fintype.card E : ℤ) + 1 -
        (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ)) : ℤ_[l]) ∧
      LinearMap.det T = (Fintype.card E : ℤ_[l]) := by
  let v := algebraMap E L (A ^ ((Fintype.card E - 1) / 6))
  let c : ℤ := (-(p : ℤ)) ^ m
  let s := twistSign L v * c
  let t := twistSign L v * (if v ^ 2 = 1 then (2 : ℤ) else -1) * c
  obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂p
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃p
  have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ (one_ne_zero : (1 : L) ≠ 0)
  have hΔA := shortCubic_discriminant_ne_zero h₂ h₃ ((map_ne_zero (algebraMap E L)).mpr hA)
  obtain ⟨u, w, hw, e, hu₀, hu, hW, he⟩ := exists_twist_conjugacy_with_parameter L E hA hΔ hΔA
  have hV : w = v := hW.trans (ratio_eq_power L E (sixth_dvd_card_sub_one p E hp hp₃ hm) hu₀ hu)
  subst w
  obtain ⟨ht, hd⟩ := trace_det_for_twist p L l E hp hp₃ hlp hm h₂ h₃ hΔ hw e he
  have hCard : Fintype.card E = p ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hm]
  have hQ : (Fintype.card E : ℤ) = c ^ 2 := by
    calc
      _ = ((p : ℤ) ^ 2) ^ m := by rw [hCard, Nat.cast_pow, pow_mul]
      _ = ((-(p : ℤ)) ^ 2) ^ m := by rw [neg_sq]
      _ = _ := by
        dsimp only [c]
        rw [← pow_mul (-(p : ℤ)) 2 m, ← pow_mul (-(p : ℤ)) m 2, Nat.mul_comm 2 m]
  have hSS : s * s = c ^ 2 := by
    rcases twistSign_cases L v with h | h <;> simp [s, h, pow_two]
  have hN := count_even p L E hp hp₃ hm hm₀ hA
  change (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ) =
    if v ^ 2 = 1 then (1 - s) ^ 2 else 1 + s + s * s at hN
  have hEq : t = (Fintype.card E : ℤ) + 1 -
      (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ) := by
    rw [hN, hQ, ← hSS]
    by_cases h : v ^ 2 = 1
    · rw [if_pos h]
      simp only [t, if_pos h, s]
      ring
    · rw [if_neg h]
      simp only [t, if_neg h, s]
      ring
  exact ⟨ht.trans (congrArg (fun z : ℤ => (Int.cast z : ℤ_[l])) hEq), hd⟩

end
end ManuscriptAudit.CubicSupersingularTatePointCount

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularTatePointCount.trace_det_eq_point_count
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
