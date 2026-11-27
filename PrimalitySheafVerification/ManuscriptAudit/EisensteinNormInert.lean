import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.FieldTheory.Finite.Basic

/-! The Eisenstein norm of a primitive pair is a unit at every inert prime power. -/

namespace ManuscriptAudit.EisensteinNormInert

variable (l : ℕ) [Fact l.Prime]

theorem norm_ne_zero {a b : ZMod l} (hl : l % 3 = 2) (hab : a ≠ 0 ∨ b ≠ 0) :
    a ^ 2 - a * b + b ^ 2 ≠ 0 := by
  intro h
  by_cases hb : b = 0
  · have ha := hab.resolve_right (fun he => he hb)
    exact (pow_ne_zero 2 ha) (by simpa [hb] using h)
  · let w := -a / b
    have hMul : (w ^ 2 + w + 1) * b ^ 2 = a ^ 2 - a * b + b ^ 2 := by
      dsimp only [w]
      field_simp [hb]
      <;> ring
    have hQ : w ^ 2 + w + 1 = 0 :=
      (mul_eq_zero.mp (hMul.trans h)).resolve_right (pow_ne_zero 2 hb)
    have hCube : w ^ 3 = 1 := sub_eq_zero.mp (by
      calc
        w ^ 3 - 1 = (w - 1) * (w ^ 2 + w + 1) := by ring
        _ = 0 := by rw [hQ, mul_zero])
    have hW : w ≠ 0 := by
      intro he
      rw [he, zero_pow (by decide : 3 ≠ 0)] at hCube
      exact zero_ne_one hCube
    have hCard : Fintype.card (ZMod l) - 1 = 3 * (l / 3) + 1 := by
      rw [ZMod.card]
      omega
    have hw := FiniteField.pow_card_sub_one_eq_one w hW
    rw [hCard, pow_add, pow_mul, hCube, one_pow, one_mul, pow_one] at hw
    have hThree : (3 : ZMod l) = 0 := by
      calc
        _ = (1 : ZMod l) ^ 2 + 1 + 1 := by norm_num
        _ = 0 := by simpa only [hw] using hQ
    have hd := (ZMod.natCast_eq_zero_iff 3 l).mp hThree
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hOne | hEq
    · exact (Fact.out : Nat.Prime l).ne_one hOne
    · omega

theorem norm_isUnit_prime_power (hl : l % 3 = 2) (a b : ℤ)
    (hab : (a : ZMod l) ≠ 0 ∨ (b : ZMod l) ≠ 0) (n : ℕ) :
    IsUnit ((a ^ 2 - a * b + b ^ 2 : ℤ) : ZMod (l ^ n)) := by
  let N := a ^ 2 - a * b + b ^ 2
  have hN : (N : ZMod l) ≠ 0 := by
    simpa only [N, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow] using norm_ne_zero l hl hab
  have hC : N.natAbs.Coprime l := by
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime l)).mpr
    intro hd
    exact hN ((ZMod.intCast_zmod_eq_zero_iff_dvd N l).mpr (Int.natCast_dvd.mpr hd))
  have hNpos : 0 ≤ N := by
    dsimp only [N]
    nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
  change IsUnit (N : ZMod (l ^ n))
  rw [← Int.natAbs_of_nonneg hNpos, Int.cast_natCast]
  exact (ZMod.isUnit_iff_coprime _ _).mpr (hC.pow_right n)

end ManuscriptAudit.EisensteinNormInert

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EisensteinNormInert.norm_isUnit_prime_power
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
