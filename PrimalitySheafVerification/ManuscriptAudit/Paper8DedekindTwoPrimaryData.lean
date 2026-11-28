import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Bounded two-primary Dedekind character and units of both Kloosterman coefficients. -/

namespace ManuscriptAudit.Paper8DedekindTwoPrimaryData

noncomputable section

def twoPrimaryCharacter (e n : ℕ) (x : ZMod 8) : ℂ :=
  (ZMod.χ₄ (ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) x) : ℂ) ^ (n / 2 + 1) *
    (ZMod.χ₈ x : ℂ) ^ e

theorem twoPrimaryCharacter_natCast (e n h : ℕ) :
    twoPrimaryCharacter e n (h : ZMod 8) =
      (ZMod.χ₄ h : ℂ) ^ (n / 2 + 1) * (ZMod.χ₈ h : ℂ) ^ e := by
  unfold twoPrimaryCharacter
  rw [map_natCast]

private theorem norm_quadratic_int_character_le {R : Type*} [CommMonoid R] {χ : MulChar R ℤ}
    (hQ : χ.IsQuadratic) (x : R) : ‖(χ x : ℂ)‖ ≤ 1 := by
  rcases hQ x with h | h | h <;> rw [h] <;> norm_num

theorem norm_twoPrimaryCharacter_le (e n : ℕ) (x : ZMod 8) :
    ‖twoPrimaryCharacter e n x‖ ≤ 1 := by
  let y := ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) x
  have h4 := norm_quadratic_int_character_le ZMod.isQuadratic_χ₄ y
  have h8 := norm_quadratic_int_character_le ZMod.isQuadratic_χ₈ x
  unfold twoPrimaryCharacter
  rw [norm_mul, norm_pow, norm_pow]
  calc
    _ ≤ (1 : ℝ) ^ (n / 2 + 1) * (1 : ℝ) ^ e :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h4 _) (pow_le_pow_left₀ (norm_nonneg _) h8 _)
        (by positivity) (by positivity)
    _ = _ := by simp

theorem isUnit_pow_two_iff_reduce_mod_two {N r : ℕ} (hr : 0 < r) (hN : N = 2 ^ r)
    (hd : 2 ∣ N) (x : ZMod N) : IsUnit x ↔ ZMod.castHom hd (ZMod 2) x ≠ 0 := by
  subst N
  letI : NeZero (2 ^ r) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  let f := ZMod.castHom hd (ZMod 2)
  have hX : f x = (x.val : ZMod 2) := by
    calc
      _ = f ((x.val : ℕ) : ZMod (2 ^ r)) := by rw [ZMod.natCast_zmod_val]
      _ = _ := map_natCast f _
  change IsUnit x ↔ f x ≠ 0
  rw [hX]
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two hr]
  exact (not_congr (ZMod.natCast_eq_zero_iff _ _)).symm

theorem even_kloosterman_coefficients_are_units (e : ℕ) {k : ℕ} (hk : k % 2 = 0)
    (d : ℤ) (hd : (2 : ℤ) ∣ d - 1) :
    let R := 8 * 2 ^ e
    IsUnit ((d : ZMod R) * (1 - (k : ZMod R))) ∧
      IsUnit ((d : ZMod R) * ((k : ZMod R) ^ 2 + 1)) := by
  let R := 8 * 2 ^ e
  have hR : R = 2 ^ (3 + e) := by
    unfold R
    rw [pow_add] <;> norm_num
  have hD : 2 ∣ R := ⟨4 * 2 ^ e, by unfold R; ring⟩
  let f := ZMod.castHom hD (ZMod 2)
  have hUnit (x : ZMod R) : IsUnit x ↔ f x ≠ 0 :=
    isUnit_pow_two_iff_reduce_mod_two (by omega) hR hD x
  have hd2 : (d : ZMod 2) = 1 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 hd
    push_cast at h
    exact sub_eq_zero.mp h
  have hk2 : (k : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff k 2).2 (Nat.dvd_of_mod_eq_zero hk)
  change IsUnit ((d : ZMod R) * (1 - (k : ZMod R))) ∧ IsUnit ((d : ZMod R) * ((k : ZMod R) ^ 2 + 1))
  constructor
  · apply (hUnit _).2
    simp only [map_mul, map_intCast, map_sub, map_one, map_natCast, hd2, hk2, sub_zero, one_mul, one_ne_zero]
  · apply (hUnit _).2
    simp only [map_mul, map_intCast, map_add, map_pow, map_one, map_natCast, hd2, hk2, zero_pow (by decide : 2 ≠ 0),
      zero_add, one_mul, one_ne_zero]

end
end ManuscriptAudit.Paper8DedekindTwoPrimaryData

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DedekindTwoPrimaryData.norm_twoPrimaryCharacter_le,
      ``ManuscriptAudit.Paper8DedekindTwoPrimaryData.even_kloosterman_coefficients_are_units] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
