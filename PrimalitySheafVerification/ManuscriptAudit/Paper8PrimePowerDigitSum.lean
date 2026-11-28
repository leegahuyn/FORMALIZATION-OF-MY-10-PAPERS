import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProductStationaryPhase

/-! Exact high-digit elimination for weighted symmetric unit sums with a stationary low digit. -/

namespace ManuscriptAudit.Paper8PrimePowerDigitSum

open Finset AddChar Paper8ProductStationaryPhase Paper8ZModDigitOrthogonality
open scoped Classical

noncomputable section

def weightedSymmetricUnitTerm {n m : ℕ} [NeZero n] [NeZero m]
    (w : ZMod m → ℂ) (a x : ZMod (n * m)) : ℂ :=
  if IsUnit x then w (reduceLowDigit x) * symmetricPhase a x else 0

def weightedSymmetricUnitSum {n m : ℕ} [NeZero n] [NeZero m]
    (w : ZMod m → ℂ) (a : ZMod (n * m)) : ℂ :=
  ∑ x : ZMod (n * m), weightedSymmetricUnitTerm w a x

theorem weighted_symmetric_sum_stationary {n m : ℕ} [NeZero n] [NeZero m]
    (hd : n ∣ m) (w : ZMod m → ℂ) (a : ZMod (n * m)) (ha : IsUnit a) :
    weightedSymmetricUnitSum w a =
      (n : ℂ) * ∑ b : ZMod m,
        if IsUnit (b.val : ZMod (n * m)) ∧
            (reduceHighDigit (b.val : ZMod (n * m)) : ZMod n) ^ 2 = 1 then
          w b * symmetricPhase a (b.val : ZMod (n * m))
        else 0 := by
  let X (b : ZMod m) := (b.val : ZMod (n * m))
  let Y (y : ZMod n) := (y.val : ZMod (n * m))
  let T (x y : ZMod (n * m)) := x + (m : ZMod (n * m)) * y
  let H (x : ZMod (n * m)) := a * (1 - (x⁻¹) ^ 2)
  let S (b : ZMod m) := ∑ y : ZMod n, weightedSymmetricUnitTerm w a (T (X b) (Y y))
  have hLow (b : ZMod m) (y : ZMod n) : reduceLowDigit (T (X b) (Y y)) = b := by
    unfold T X
    simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
  have hHigh (y : ZMod n) : (((Y y).val : ℕ) : ZMod n) = y := by
    rw [← reduceHighDigit_apply]
    unfold Y
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hR (b : ZMod m) :
      S b = (n : ℂ) *
        if IsUnit (X b) ∧ (reduceHighDigit (X b) : ZMod n) ^ 2 = 1 then
          w b * symmetricPhase a (X b) else 0 := by
    by_cases hb : IsUnit (X b)
    · have hPoint (y : ZMod n) : weightedSymmetricUnitTerm w a (T (X b) (Y y)) =
          (w b * symmetricPhase a (X b)) * ZMod.stdAddChar (reduceHighDigit (H (X b)) * y) := by
        unfold weightedSymmetricUnitTerm
        rw [if_pos ((unit_shift_high_digit hd (X b) (Y y)).2 hb), hLow]
        unfold T
        rw [symmetricPhase_high_digit hd a (X b) (Y y) hb, hHigh]
        exact (mul_assoc _ _ _).symm
      have hStation : reduceHighDigit (H (X b)) = 0 ↔ (reduceHighDigit (X b) : ZMod n) ^ 2 = 1 :=
        high_digit_stationary_condition a (X b) ha hb
      unfold S
      simp_rw [hPoint, ← Finset.mul_sum, mul_comm (reduceHighDigit (H (X b)))]
      rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]
      simp only [hStation, hb, true_and]
      split_ifs <;> push_cast <;> ring
    · have hZero (y : ZMod n) : weightedSymmetricUnitTerm w a (T (X b) (Y y)) = 0 := by
        unfold weightedSymmetricUnitTerm
        exact if_neg fun h => hb ((unit_shift_high_digit hd (X b) (Y y)).1 h)
      simp [S, hZero, hb]
  have hSum : weightedSymmetricUnitSum w a = ∑ b : ZMod m, S b := by
    unfold weightedSymmetricUnitSum
    rw [sum_residue_digits, Finset.sum_comm]
    simp only [T, S, X, Y, Nat.cast_add, Nat.cast_mul]
  rw [hSum]
  simp_rw [hR, ← Finset.mul_sum, X]

end
end ManuscriptAudit.Paper8PrimePowerDigitSum

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8PrimePowerDigitSum.weighted_symmetric_sum_stationary
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
