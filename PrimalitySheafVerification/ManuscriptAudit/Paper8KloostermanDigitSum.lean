import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8KloostermanProductPhase

/-! Exact high-digit elimination for weighted Kloosterman sums with unequal coefficients. -/

namespace ManuscriptAudit.Paper8KloostermanDigitSum

open Finset AddChar Paper8ProductStationaryPhase Paper8ZModDigitOrthogonality Paper8KloostermanProductPhase
open scoped Classical

noncomputable section

def weightedKloostermanUnitTerm {n m : ℕ} [NeZero n] [NeZero m]
    (w : ZMod m → ℂ) (a b x : ZMod (n * m)) : ℂ :=
  if IsUnit x then w (reduceLowDigit x) * kloostermanPhase a b x else 0

def weightedKloostermanUnitSum {n m : ℕ} [NeZero n] [NeZero m]
    (w : ZMod m → ℂ) (a b : ZMod (n * m)) : ℂ :=
  ∑ x : ZMod (n * m), weightedKloostermanUnitTerm w a b x

theorem weighted_kloosterman_sum_stationary {n m : ℕ} [NeZero n] [NeZero m]
    (hd : n ∣ m) (w : ZMod m → ℂ) (a b : ZMod (n * m)) (ha : IsUnit a) :
    weightedKloostermanUnitSum w a b =
      (n : ℂ) * ∑ z : ZMod m,
        if IsUnit (z.val : ZMod (n * m)) ∧
            (reduceHighDigit (z.val : ZMod (n * m)) : ZMod n) ^ 2 = (reduceHighDigit a)⁻¹ * reduceHighDigit b then
          w z * kloostermanPhase a b (z.val : ZMod (n * m))
        else 0 := by
  let X (z : ZMod m) := (z.val : ZMod (n * m))
  let Y (y : ZMod n) := (y.val : ZMod (n * m))
  let T (x y : ZMod (n * m)) := x + (m : ZMod (n * m)) * y
  let H (x : ZMod (n * m)) := a - b * (x⁻¹) ^ 2
  let S (z : ZMod m) := ∑ y : ZMod n, weightedKloostermanUnitTerm w a b (T (X z) (Y y))
  have hLow (z : ZMod m) (y : ZMod n) : reduceLowDigit (T (X z) (Y y)) = z := by
    unfold T X
    simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
  have hHigh (y : ZMod n) : (((Y y).val : ℕ) : ZMod n) = y := by
    rw [← reduceHighDigit_apply]
    unfold Y
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hR (z : ZMod m) :
      S z = (n : ℂ) *
        if IsUnit (X z) ∧ (reduceHighDigit (X z) : ZMod n) ^ 2 = (reduceHighDigit a)⁻¹ * reduceHighDigit b then
          w z * kloostermanPhase a b (X z) else 0 := by
    by_cases hb : IsUnit (X z)
    · have hPoint (y : ZMod n) : weightedKloostermanUnitTerm w a b (T (X z) (Y y)) =
          (w z * kloostermanPhase a b (X z)) * ZMod.stdAddChar (reduceHighDigit (H (X z)) * y) := by
        unfold weightedKloostermanUnitTerm
        rw [if_pos ((unit_shift_high_digit hd (X z) (Y y)).2 hb), hLow]
        unfold T
        rw [kloostermanPhase_high_digit hd a b (X z) (Y y) hb, hHigh]
        exact (mul_assoc _ _ _).symm
      have hStation : reduceHighDigit (H (X z)) = 0 ↔ (reduceHighDigit (X z) : ZMod n) ^ 2 = (reduceHighDigit a)⁻¹ * reduceHighDigit b :=
        kloosterman_high_digit_stationary a b (X z) ha hb
      unfold S
      simp_rw [hPoint, ← Finset.mul_sum, mul_comm (reduceHighDigit (H (X z)))]
      rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n), ZMod.card]
      simp only [hStation, hb, true_and]
      split_ifs <;> push_cast <;> ring
    · have hZero (y : ZMod n) : weightedKloostermanUnitTerm w a b (T (X z) (Y y)) = 0 := by
        unfold weightedKloostermanUnitTerm
        exact if_neg fun h => hb ((unit_shift_high_digit hd (X z) (Y y)).1 h)
      simp [S, hZero, hb]
  have hSum : weightedKloostermanUnitSum w a b = ∑ z : ZMod m, S z := by
    unfold weightedKloostermanUnitSum
    rw [sum_residue_digits, Finset.sum_comm]
    simp only [T, S, X, Y, Nat.cast_add, Nat.cast_mul]
  rw [hSum]
  simp_rw [hR, ← Finset.mul_sum, X]

theorem norm_weighted_kloosterman_sum_stationary_count {n m : ℕ} [NeZero n] [NeZero m]
    (hd : n ∣ m) (w : ZMod m → ℂ) (hw : ∀ z, ‖w z‖ ≤ 1)
    (a b : ZMod (n * m)) (ha : IsUnit a) :
    ‖weightedKloostermanUnitSum w a b‖ ≤ (n : ℝ) *
      ((Finset.univ.filter (fun z : ZMod m =>
        (reduceHighDigit (z.val : ZMod (n * m)) : ZMod n) ^ 2 =
          (reduceHighDigit a)⁻¹ * reduceHighDigit b)).card : ℝ) := by
  let X (z : ZMod m) := (z.val : ZMod (n * m))
  let p (z : ZMod m) : Prop :=
    (reduceHighDigit (X z) : ZMod n) ^ 2 = (reduceHighDigit a)⁻¹ * reduceHighDigit b
  let F (z : ZMod m) := if IsUnit (X z) ∧ p z then w z * kloostermanPhase a b (X z) else 0
  have hN (x : ZMod (n * m)) : ‖kloostermanPhase a b x‖ = 1 := by
    unfold kloostermanPhase
    have hPos : 0 < ringChar (ZMod (n * m)) := by
      rw [ZMod.ringChar_zmod_n]
      exact Nat.pos_of_ne_zero (NeZero.ne _)
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((ZMod.stdAddChar (N := n * m)).val_mem_rootsOfUnity (a * x + b * x⁻¹) hPos)
    simpa only [IsUnit.unit_spec] using h
  have hPoint (z : ZMod m) : ‖F z‖ ≤ if p z then (1 : ℝ) else 0 := by
    unfold F
    by_cases hz : p z
    · rw [if_pos hz]
      by_cases hu : IsUnit (X z)
      · rw [if_pos (And.intro hu hz), norm_mul, hN, mul_one]
        exact hw z
      · rw [if_neg (fun h => hu h.1), norm_zero]
        norm_num
    · simp [hz]
  rw [weighted_kloosterman_sum_stationary hd w a b ha]
  change ‖(n : ℂ) * (∑ z : ZMod m, F z)‖ ≤ (n : ℝ) * ((Finset.univ.filter p).card : ℝ)
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (n : ℝ) * ∑ z : ZMod m, ‖F z‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Nat.cast_nonneg _)
    _ ≤ (n : ℝ) * ∑ z : ZMod m, if p z then (1 : ℝ) else 0 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _ => hPoint z)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end
end ManuscriptAudit.Paper8KloostermanDigitSum

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8KloostermanDigitSum.norm_weighted_kloosterman_sum_stationary_count
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
