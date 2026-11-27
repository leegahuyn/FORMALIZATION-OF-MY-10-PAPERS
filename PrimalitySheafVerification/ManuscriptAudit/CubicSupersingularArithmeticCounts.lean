import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularTwistPointCounts

/-! The point count is determined by the literal sixth-power residue of the coefficient. -/

namespace ManuscriptAudit.CubicSupersingularArithmeticCounts

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard CubicCubeRotation
open CubicNonsplitThreeAdicTrace CubicSexticRotation CubicSupersingularUnitFrobenius
open CubicSupersingularTwistFrobenius CubicSupersingularTwistPointCounts

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E] [Algebra E L]

theorem sixth_dvd_card_sub_one (hp : 5 ≤ p) (hp₃ : p % 3 = 2)
    {m : ℕ} (hm : Module.finrank (ZMod p) E = 2 * m) :
    6 ∣ Fintype.card E - 1 := by
  have hP₂ : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd (Fact.out : p.Prime) with h | h <;> omega
  have hP₆ : p % 6 = 5 := by omega
  have hP : p ^ 2 % 6 = 1 := by rw [Nat.pow_mod, hP₆]
  have hCard : Fintype.card E = p ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hm]
  have hQ : Fintype.card E % 6 = 1 := by
    rw [hCard, pow_mul, Nat.pow_mod, hP, one_pow] <;> decide
  omega

/-- Exact native point-count formula for every nonzero twist over an even-degree base. -/
theorem count_even (hp : 5 ≤ p) (hp₃ : p % 3 = 2)
    {m : ℕ} (hm : Module.finrank (ZMod p) E = 2 * m) (hm₀ : 0 < m)
    {A : E} (hA : A ≠ 0) :
    let v := algebraMap E L (A ^ ((Fintype.card E - 1) / 6))
    let s : ℤ := twistSign L v * (-(p : ℤ)) ^ m
    (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ) =
      if v ^ 2 = 1 then (1 - s) ^ 2 else 1 + s + s * s := by
  let v := algebraMap E L (A ^ ((Fintype.card E - 1) / 6))
  let c : ℤ := (-(p : ℤ)) ^ m
  let s : ℤ := twistSign L v * c
  change (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ) =
    if v ^ 2 = 1 then (1 - s) ^ 2 else 1 + s + s * s
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
  have hpc : (p : ℤ) ∣ c := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm₀)
    refine ⟨-((-(p : ℤ)) ^ k), ?_⟩
    dsimp [c]
    rw [hk, pow_succ]
    ring
  have hs : (p : ℤ) ∣ s := dvd_mul_of_dvd_right hpc _
  have hF (P : UnitPoints L) : arithmeticUnit E L P = c • P := by
    rw [arithmeticUnit_eq_scalar E L p hp hp₃ hm] <;> rfl
  apply count_from_rotation p L E hp hp₃ h₂ h₃ hΔ (square_cube L hw) s hs e
  intro P
  rw [he, hF, sextic_eq_signed_rotation L hw hΔ]
  change e (twistSign L v • rotate (v ^ 2) (square_cube L hw) hΔ (c • P)) =
    e (s • rotate (v ^ 2) (square_cube L hw) hΔ P)
  rw [map_zsmul, smul_smul]

end
end ManuscriptAudit.CubicSupersingularArithmeticCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSupersingularArithmeticCounts.sixth_dvd_card_sub_one,
      ``ManuscriptAudit.CubicSupersingularArithmeticCounts.count_even] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
