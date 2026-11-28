import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimePowerStationaryPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8ZModDigitOrthogonality

/-! Exact two-branch stationary cancellation for symmetric unit sums at even odd-prime powers. -/

namespace ManuscriptAudit.Paper8EvenPrimePowerUnitSum

open Finset AddChar Paper8PrimePowerStationaryPhase Paper8ZModDigitOrthogonality
open scoped Classical

noncomputable section

def symmetricUnitTerm {n : ℕ} [NeZero n] (a x : ZMod n) : ℂ :=
  if IsUnit x then ZMod.stdAddChar (a * (x + x⁻¹)) else 0

def symmetricUnitSum {n : ℕ} [NeZero n] (a : ZMod n) : ℂ :=
  ∑ x : ZMod n, symmetricUnitTerm a x

private theorem isUnit_of_mul_one {R : Type*} [CommMonoid R] {a b : R} (h : a * b = 1) :
    IsUnit a :=
  ⟨⟨a, b, h, by simpa only [mul_comm] using h⟩, rfl⟩

private theorem isUnit_add_sqzero {n : ℕ} (x t : ZMod n) (ht : t ^ 2 = 0) :
    IsUnit (x + t) ↔ IsUnit x := by
  have hShift (a b : ZMod n) (hSquare : b ^ 2 = 0) (ha : IsUnit a) : IsUnit (a + b) :=
    isUnit_of_mul_one (linear_nilpotent_inverse (ZMod.mul_inv_of_unit a ha) hSquare)
  constructor
  · intro h
    have hNeg : (-t) ^ 2 = 0 := by rwa [neg_sq]
    simpa only [add_neg_cancel_right] using hShift (x + t) (-t) hNeg h
  · exact hShift x t ht

private theorem isUnit_nat_lift {p r : ℕ} (hPrime : p.Prime) (hr : 0 < r) (x : ℕ) :
    IsUnit (x : ZMod (p ^ r * p ^ r)) ↔ IsUnit (x : ZMod (p ^ r)) := by
  rw [← pow_add]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hPrime (by omega),
    ZMod.isUnit_natCast_iff_not_dvd_pow hPrime hr]

private theorem norm_stdAddChar {n : ℕ} [NeZero n] (a : ZMod n) : ‖ZMod.stdAddChar a‖ = 1 := by
  have hn : 0 < ringChar (ZMod n) := by rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne _)
  exact Complex.norm_eq_one_of_mem_rootsOfUnity ((ZMod.stdAddChar (N := n)).val_mem_rootsOfUnity a hn)

theorem norm_symmetricUnitSum_even_prime_power {p r : ℕ} (hPrime : p.Prime) (hp : p ≠ 2) (hr : 0 < r)
    (a : ZMod (p ^ r * p ^ r)) (hA : IsUnit a) :
    letI : NeZero (p ^ r * p ^ r) := ⟨mul_ne_zero (pow_ne_zero _ hPrime.ne_zero)
      (pow_ne_zero _ hPrime.ne_zero)⟩
    ‖symmetricUnitSum a‖ ≤ 2 * ((p ^ r : ℕ) : ℝ) := by
  let k := p ^ r
  have hk : 0 < k := pow_pos hPrime.pos _
  letI : NeZero k := ⟨hk.ne'⟩
  letI : NeZero (k * k) := ⟨mul_ne_zero hk.ne' hk.ne'⟩
  let μ := @reduceHighDigit k k
  let Y (y : ZMod k) : ZMod (k * k) := (k : ZMod (k * k)) * (y.val : ZMod (k * k))
  let X (x : ZMod k) : ZMod (k * k) := (x.val : ZMod (k * k))
  let S (x : ZMod k) := ∑ y : ZMod k, symmetricUnitTerm a (X x + Y y)
  have hSquare (y : ZMod k) : (Y y) ^ 2 = 0 := by
    unfold Y
    rw [mul_pow, ← Nat.cast_pow, pow_two k, ZMod.natCast_self, zero_mul]
  have hRed (x : ZMod k) : μ (X x) = x := by
    dsimp only [μ, X]
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hL (x : ZMod k) : IsUnit (X x) ↔ IsUnit x := by
    have h := isUnit_nat_lift hPrime hr x.val
    change IsUnit (X x) ↔ IsUnit (x.val : ZMod k) at h
    rwa [ZMod.natCast_zmod_val] at h
  have hA' : IsUnit (μ a) := hA.map μ
  have hNorm (x : ZMod k) : ‖S x‖ ≤ if x ^ 2 = 1 then (k : ℝ) else 0 := by
    by_cases hx : IsUnit x
    · have hxL := (hL x).2 hx
      have hRedInv : μ (X x)⁻¹ = x⁻¹ := by
        have h := congrArg μ (ZMod.mul_inv_of_unit (X x) hxL)
        rw [map_mul, map_one, hRed] at h
        exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h).symm
      let B := a * (X x + (X x)⁻¹)
      let C := a * (1 - ((X x)⁻¹) ^ 2)
      have hStation : μ C = 0 ↔ x ^ 2 = 1 := by
        have hRedC : μ C = μ a * (1 - (x⁻¹) ^ 2) := by
          unfold C
          rw [map_mul, map_sub, map_one, map_pow, hRedInv]
        have hProd : x ^ 2 * (x⁻¹) ^ 2 = 1 := by rw [← mul_pow, ZMod.mul_inv_of_unit x hx, one_pow]
        rw [hRedC]
        constructor
        · intro h
          have hh := congrArg (fun u : ZMod k => (μ a)⁻¹ * u) h
          change (μ a)⁻¹ * (μ a * (1 - (x⁻¹) ^ 2)) = (μ a)⁻¹ * 0 at hh
          rw [← mul_assoc, ZMod.inv_mul_of_unit (μ a) hA', one_mul, mul_zero] at hh
          have hi := (sub_eq_zero.mp hh).symm
          simpa only [hi, mul_one] using hProd
        · intro h
          have hi : (x⁻¹) ^ 2 = 1 := by simpa only [h, one_mul] using hProd
          rw [hi, sub_self, mul_zero]
      have hAt (y : ZMod k) :
          symmetricUnitTerm a (X x + Y y) =
            ZMod.stdAddChar B * ZMod.stdAddChar ((k : ZMod (k * k)) * C * (y.val : ZMod (k * k))) := by
        have hu := (isUnit_add_sqzero (X x) (Y y) (hSquare y)).2 hxL
        have hInv := linear_nilpotent_inverse (ZMod.mul_inv_of_unit (X x) hxL) (hSquare y)
        unfold symmetricUnitTerm
        rw [if_pos hu, ZMod.inv_eq_of_mul_eq_one _ _ _ hInv, ← AddChar.map_add_eq_mul]
        congr 1
        unfold B C Y
        ring
      have hEval : S x = ZMod.stdAddChar B * (if x ^ 2 = 1 then (k : ℂ) else 0) := by
        unfold S
        simp_rw [hAt, ← Finset.mul_sum, sum_stdAddChar_high_digit]
        change _ = _
        rw [show reduceHighDigit C = 0 ↔ x ^ 2 = 1 from hStation]
      rw [hEval, norm_mul, norm_stdAddChar, one_mul]
      split_ifs <;> simp
    · have hxL : ¬ IsUnit (X x) := fun h => hx ((hL x).1 h)
      have h0 : S x = 0 := by
        unfold S symmetricUnitTerm
        apply Finset.sum_eq_zero
        intro y _
        exact if_neg (fun h => hxL ((isUnit_add_sqzero (X x) (Y y) (hSquare y)).1 h))
      rw [h0, norm_zero]
      split_ifs <;> positivity
  have hSum : symmetricUnitSum a = ∑ x : ZMod k, S x := by
    unfold symmetricUnitSum
    rw [sum_residue_digits, Finset.sum_comm]
    simp only [S, X, Y, Nat.cast_add, Nat.cast_mul]
  let R := Finset.univ.filter (fun x : ZMod k => x ^ 2 = 1)
  have hSub : R ⊆ ({1, -1} : Finset (ZMod k)) := by
    intro x hx
    have h : x ^ 2 = 1 := (Finset.mem_filter.mp hx).2
    have hEq := (prime_pow_sq_eq_one_iff hPrime hp x).1 h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hEq
  have hCard : R.card ≤ 2 :=
    (Finset.card_le_card hSub).trans (by
      calc
        _ ≤ ({(-1 : ZMod k)} : Finset (ZMod k)).card + 1 := Finset.card_insert_le _ _
        _ = _ := by simp)
  rw [hSum]
  calc
    _ ≤ ∑ x : ZMod k, ‖S x‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod k, if x ^ 2 = 1 then (k : ℝ) else 0 := Finset.sum_le_sum (fun x _ => hNorm x)
    _ = (R.card : ℝ) * (k : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) (Nat.cast_nonneg _)

end
end ManuscriptAudit.Paper8EvenPrimePowerUnitSum

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8EvenPrimePowerUnitSum.norm_symmetricUnitSum_even_prime_power
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
