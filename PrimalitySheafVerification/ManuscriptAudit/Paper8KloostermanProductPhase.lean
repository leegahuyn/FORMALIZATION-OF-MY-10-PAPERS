import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProductStationaryPhase

/-! Exact product-digit stationary criterion for a Kloosterman term with two unit coefficients. -/

namespace ManuscriptAudit.Paper8KloostermanProductPhase

open Paper8ProductStationaryPhase Paper8PrimePowerStationaryPhase Paper8ZModDigitOrthogonality

noncomputable section

def kloostermanPhase {n : ℕ} [NeZero n] (a b x : ZMod n) : ℂ :=
  ZMod.stdAddChar (a * x + b * x⁻¹)

theorem kloostermanPhase_high_digit {n m : ℕ} [NeZero n] [NeZero m] (hd : n ∣ m)
    (a b x t : ZMod (n * m)) (hx : IsUnit x) :
    kloostermanPhase a b (x + (m : ZMod (n * m)) * t) =
      kloostermanPhase a b x *
        ZMod.stdAddChar (reduceHighDigit (a - b * (x⁻¹) ^ 2) * (t.val : ZMod n)) := by
  let T := (m : ZMod (n * m)) * t
  let C := a - b * (x⁻¹) ^ 2
  have hInv := linear_nilpotent_inverse (ZMod.mul_inv_of_unit x hx) (high_digit_sq_zero hd t)
  change ZMod.stdAddChar (a * (x + T) + b * (x + T)⁻¹) =
    ZMod.stdAddChar (a * x + b * x⁻¹) * ZMod.stdAddChar (reduceHighDigit C * (t.val : ZMod n))
  rw [ZMod.inv_eq_of_mul_eq_one _ _ _ hInv]
  have hArg : a * (x + T) + b * (x⁻¹ - (x⁻¹) ^ 2 * T) = a * x + b * x⁻¹ +
      (m : ZMod (n * m)) * C * (t.val : ZMod (n * m)) := by
    rw [ZMod.natCast_zmod_val]
    unfold C T
    ring
  rw [hArg, AddChar.map_add_eq_mul, stdAddChar_high_digit_nat]

theorem kloosterman_high_digit_stationary {n m : ℕ} (a b x : ZMod (n * m)) (ha : IsUnit a) (hx : IsUnit x) :
    reduceHighDigit (a - b * (x⁻¹) ^ 2) = 0 ↔
      (reduceHighDigit x : ZMod n) ^ 2 = (reduceHighDigit a : ZMod n)⁻¹ * reduceHighDigit b := by
  let f : ZMod (n * m) →+* ZMod n := @reduceHighDigit n m
  have hInv : f (x⁻¹) = (f x)⁻¹ := by
    have h := congrArg f (ZMod.mul_inv_of_unit x hx)
    rw [map_mul, map_one] at h
    exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h).symm
  let X := f x
  let A := f a
  let B := f b
  have hX : X ^ 2 * (X⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, ZMod.mul_inv_of_unit X (hx.map f), one_pow]
  have hX' : (X⁻¹) ^ 2 * X ^ 2 = 1 := by simpa only [mul_comm] using hX
  have hA : IsUnit A := ha.map f
  change f (a - b * (x⁻¹) ^ 2) = 0 ↔ X ^ 2 = A⁻¹ * B
  rw [map_sub, map_mul, map_pow, hInv, sub_eq_zero]
  change A = B * (X⁻¹) ^ 2 ↔ X ^ 2 = A⁻¹ * B
  constructor
  · intro h
    calc
      _ = A⁻¹ * (A * X ^ 2) := by rw [← mul_assoc, ZMod.inv_mul_of_unit A hA, one_mul]
      _ = A⁻¹ * (B * ((X⁻¹) ^ 2 * X ^ 2)) := by rw [h]; ring
      _ = _ := by rw [hX', mul_one]
  · intro h
    calc
      _ = (A * X ^ 2) * (X⁻¹) ^ 2 := by rw [mul_assoc, hX, mul_one]
      _ = _ := by rw [h, ← mul_assoc A A⁻¹ B, ZMod.mul_inv_of_unit A hA, one_mul]

end
end ManuscriptAudit.Paper8KloostermanProductPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8KloostermanProductPhase.kloostermanPhase_high_digit,
      ``ManuscriptAudit.Paper8KloostermanProductPhase.kloosterman_high_digit_stationary] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
