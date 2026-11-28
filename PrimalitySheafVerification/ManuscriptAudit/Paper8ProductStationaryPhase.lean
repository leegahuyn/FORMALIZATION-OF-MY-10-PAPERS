import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimePowerStationaryPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8ZModDigitOrthogonality

/-! The local high-digit stationary identity and independence of the chosen lift. -/

namespace ManuscriptAudit.Paper8ProductStationaryPhase

open Finset AddChar Paper8PrimePowerStationaryPhase Paper8ZModDigitOrthogonality

noncomputable section

def reduceLowDigit {n m : ℕ} : ZMod (n * m) →+* ZMod m :=
  ZMod.castHom (dvd_mul_left m n) (ZMod m)

def symmetricPhase {n : ℕ} [NeZero n] (a x : ZMod n) : ℂ :=
  ZMod.stdAddChar (a * (x + x⁻¹))

theorem same_low_digit_diff {n m : ℕ} {x y : ZMod (n * m)}
    (h : reduceLowDigit x = reduceLowDigit y) :
    ∃ t : ZMod (n * m), x = y + (m : ZMod (n * m)) * t := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  have hZ : ((a - b : ℤ) : ZMod m) = 0 := by
    push_cast
    change (a : ZMod m) - (b : ZMod m) = 0
    have hh : (a : ZMod m) = (b : ZMod m) := by simpa only [map_intCast] using h
    rw [hh, sub_self]
  obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 hZ
  refine ⟨(q : ZMod (n * m)), ?_⟩
  have hQ := congrArg (fun z : ℤ => (z : ZMod (n * m))) hq
  push_cast at hQ
  linear_combination hQ

theorem high_digit_sq_zero {n m : ℕ} (hd : n ∣ m) (t : ZMod (n * m)) :
    ((m : ZMod (n * m)) * t) ^ 2 = 0 := by
  have hd' : n * m ∣ m ^ 2 := by
    obtain ⟨q, hq⟩ := hd
    refine ⟨q, ?_⟩
    calc
      _ = m * m := by ring
      _ = (n * q) * m := by nth_rw 1 [hq]
      _ = _ := by ring
  rw [mul_pow, ← Nat.cast_pow, (ZMod.natCast_eq_zero_iff _ _).2 hd', zero_mul]

theorem unit_shift_high_digit {n m : ℕ} (hd : n ∣ m) (x t : ZMod (n * m)) :
    IsUnit (x + (m : ZMod (n * m)) * t) ↔ IsUnit x := by
  have hShift (x y : ZMod (n * m)) (hy : y ^ 2 = 0) (hx : IsUnit x) : IsUnit (x + y) := by
    have hh := linear_nilpotent_inverse (ZMod.mul_inv_of_unit x hx) hy
    exact ⟨⟨_, _, hh, by simpa only [mul_comm] using hh⟩, rfl⟩
  have hT := high_digit_sq_zero hd t
  constructor
  · intro h
    have hSq : (-((m : ZMod (n * m)) * t)) ^ 2 = 0 := by rwa [neg_sq]
    simpa only [add_neg_cancel_right] using hShift _ _ hSq h
  · exact hShift _ _ hT

theorem high_digit_stationary_condition {n m : ℕ} (a x : ZMod (n * m)) (ha : IsUnit a) (hx : IsUnit x) :
    reduceHighDigit (a * (1 - (x⁻¹) ^ 2)) = 0 ↔ (reduceHighDigit x : ZMod n) ^ 2 = 1 := by
  let f : ZMod (n * m) →+* ZMod n := @reduceHighDigit n m
  have hxInv : f (x⁻¹) = (f x)⁻¹ := by
    have h := congrArg f (ZMod.mul_inv_of_unit x hx)
    change f (x * x⁻¹) = f 1 at h
    rw [map_mul, map_one] at h
    exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h).symm
  have hProd : (f x) ^ 2 * ((f x)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, ZMod.mul_inv_of_unit _ (hx.map f), one_pow]
  change f (a * (1 - (x⁻¹) ^ 2)) = 0 ↔ (f x) ^ 2 = 1
  rw [map_mul, map_sub, map_one, map_pow, hxInv]
  constructor
  · intro h
    have h' := congrArg (fun z : ZMod n => (f a)⁻¹ * z) h
    change (f a)⁻¹ * (f a * (1 - ((f x)⁻¹) ^ 2)) = (f a)⁻¹ * 0 at h'
    rw [← mul_assoc, ZMod.inv_mul_of_unit _ (ha.map f), one_mul, mul_zero] at h'
    have hI := (sub_eq_zero.mp h').symm
    simpa only [hI, mul_one] using hProd
  · intro h
    have hI : ((f x)⁻¹) ^ 2 = 1 := by simpa only [h, one_mul] using hProd
    rw [hI, sub_self, mul_zero]

theorem symmetricPhase_high_digit {n m : ℕ} [NeZero n] [NeZero m] (hd : n ∣ m)
    (a x t : ZMod (n * m)) (hx : IsUnit x) :
    symmetricPhase a (x + (m : ZMod (n * m)) * t) =
      symmetricPhase a x *
        ZMod.stdAddChar (reduceHighDigit (a * (1 - (x⁻¹) ^ 2)) * (t.val : ZMod n)) := by
  let T := (m : ZMod (n * m)) * t
  let C := a * (1 - (x⁻¹) ^ 2)
  have hInv := linear_nilpotent_inverse (ZMod.mul_inv_of_unit x hx) (high_digit_sq_zero hd t)
  change ZMod.stdAddChar (a * ((x + T) + (x + T)⁻¹)) =
    ZMod.stdAddChar (a * (x + x⁻¹)) * ZMod.stdAddChar (reduceHighDigit C * (t.val : ZMod n))
  rw [ZMod.inv_eq_of_mul_eq_one _ _ _ hInv]
  have hArg : a * ((x + T) + (x⁻¹ - (x⁻¹) ^ 2 * T)) = a * (x + x⁻¹) +
      (m : ZMod (n * m)) * C * (t.val : ZMod (n * m)) := by
    rw [ZMod.natCast_zmod_val]
    dsimp only [T, C]
    ring
  rw [hArg, AddChar.map_add_eq_mul, stdAddChar_high_digit_nat]

theorem symmetricPhase_eq_of_stationary_lift {n m : ℕ} [NeZero n] [NeZero m]
    (hd : n ∣ m) (a x y : ZMod (n * m)) (hx : IsUnit x)
    (hStation : reduceHighDigit (a * (1 - (x⁻¹) ^ 2)) = 0)
    (hLow : reduceLowDigit y = reduceLowDigit x) :
    symmetricPhase a y = symmetricPhase a x := by
  obtain ⟨t, ht⟩ := same_low_digit_diff hLow
  rw [ht, symmetricPhase_high_digit hd a x t hx, hStation, zero_mul, AddChar.map_zero_eq_one, mul_one]

end
end ManuscriptAudit.Paper8ProductStationaryPhase

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8ProductStationaryPhase.symmetricPhase_eq_of_stationary_lift
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
