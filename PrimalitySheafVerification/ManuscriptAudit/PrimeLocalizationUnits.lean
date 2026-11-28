import Lean.Util.CollectAxioms
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.RingTheory.Localization.Away.Basic

/-! Every unit after inverting a prime element of an integral domain is
a unit of the original ring times an integral power of the prime. -/

namespace ManuscriptAudit.PrimeLocalizationUnits

open scoped nonZeroDivisors

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] (p : R)

abbrev S := Localization.Away p

/-- The image of the inverted prime as an actual unit. -/
def primeUnit : (S p)ˣ := (IsLocalization.Away.algebraMap_isUnit (S := S p) p).unit

theorem primeUnit_val : ((primeUnit p : (S p)ˣ) : S p) = algebraMap R (S p) p :=
  (IsLocalization.Away.algebraMap_isUnit (S := S p) p).unit_spec

/-- The homomorphism of unit groups induced by localization. -/
def mapUnit : Rˣ →* (S p)ˣ := Units.map (algebraMap R (S p)).toMonoidHom

theorem mapUnit_val (v : Rˣ) : ((mapUnit p v : (S p)ˣ) : S p) = algebraMap R (S p) v :=
  rfl

private theorem map_injective (hp : Prime p) : Function.Injective (algebraMap R (S p)) :=
  IsLocalization.injective (M := Submonoid.powers p) (S p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hp.ne_zero)

/-- A unit of the principal-open coordinate ring has a numerator associated
to a power of the omitted prime. Its denominator gives the integer exponent. -/
theorem exists_lift_mul_zpow (hp : Prime p) (s : (S p)ˣ) :
    ∃ (v : Rˣ) (n : ℤ), s = mapUnit p v * (primeUnit p) ^ n := by
  let f := algebraMap R (S p)
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (x := p) (s : S p)
  obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj (x := p) (↑(s⁻¹) : S p)
  change (s : S p) * f p ^ n = f a at ha
  change (↑(s⁻¹) : S p) * f p ^ m = f b at hb
  have hab : a * b = p ^ (n + m) := by
    apply map_injective p hp
    change f (a * b) = f (p ^ (n + m))
    rw [map_mul, ← ha, ← hb, map_pow, pow_add]
    calc
      _ = ((s : S p) * ↑(s⁻¹)) * (f p ^ n * f p ^ m) := by ac_rfl
      _ = _ := by rw [Units.mul_inv, one_mul]
  obtain ⟨i, -, v, hv⟩ := (dvd_prime_pow hp (n + m)).mp ⟨b, hab.symm⟩
  have hs : s * (primeUnit p) ^ n * mapUnit p v = (primeUnit p) ^ i := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, primeUnit_val, mapUnit_val]
    change (s : S p) * f p ^ n * f v = f p ^ i
    rw [ha, ← map_mul, hv, map_pow]
  refine ⟨v⁻¹, (i : ℤ) - (n : ℤ), ?_⟩
  calc
    s = (primeUnit p) ^ i * ((primeUnit p) ^ n * mapUnit p v)⁻¹ :=
      (eq_mul_inv_iff_mul_eq).2 (by simpa only [mul_assoc] using hs)
    _ = _ := by
      rw [mul_inv_rev, map_inv, zpow_sub, zpow_natCast, zpow_natCast, div_eq_mul_inv]
      ac_rfl

private theorem power_eq_lift_only_zero (hp : Prime p) (v : Rˣ) (n : ℕ)
    (h : (primeUnit p) ^ n = mapUnit p v) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    exfalso
    have hv : p ^ (n + 1) = (v : R) := by
      apply map_injective p hp
      have hh := congrArg (fun w : (S p)ˣ => (w : S p)) h
      simpa only [Units.val_pow_eq_pow_val, primeUnit_val, mapUnit_val, map_pow] using hh
    have hd : p ∣ (v : R) := ⟨p ^ n, by rw [← hv, pow_succ']⟩
    exact hp.not_isUnit (isUnit_iff_dvd_one.mpr (hd.trans (isUnit_iff_dvd_one.mp v.isUnit)))

private theorem zpower_eq_lift_only_zero (hp : Prime p) (v : Rˣ) (n : ℤ)
    (h : (primeUnit p) ^ n = mapUnit p v) : n = 0 := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast] at h
    rw [power_eq_lift_only_zero p hp v m h] <;> rfl
  · rw [zpow_neg, zpow_natCast] at h
    have hi : (primeUnit p) ^ m = mapUnit p v⁻¹ := by
      simpa only [inv_inv, map_inv] using congrArg Inv.inv h
    rw [power_eq_lift_only_zero p hp v⁻¹ m hi] <;> rfl

/-- The exponent is unique even when the lift is allowed to vary. -/
theorem exponent_unique (hp : Prime p) (u v : Rˣ) (a b : ℤ)
    (h : mapUnit p u * (primeUnit p) ^ a = mapUnit p v * (primeUnit p) ^ b) : a = b := by
  apply sub_eq_zero.mp
  apply zpower_eq_lift_only_zero p hp (u⁻¹ * v)
  rw [zpow_sub, div_eq_mul_inv, map_mul, map_inv]
  calc
    _ = (mapUnit p u)⁻¹ * (mapUnit p u * (primeUnit p) ^ a) * ((primeUnit p) ^ b)⁻¹ := by
      rw [← mul_assoc (mapUnit p u)⁻¹, inv_mul_cancel, one_mul]
    _ = _ := by rw [h, mul_assoc, mul_inv_cancel_right]

end

end ManuscriptAudit.PrimeLocalizationUnits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PrimeLocalizationUnits.primeUnit_val,
      ``ManuscriptAudit.PrimeLocalizationUnits.exists_lift_mul_zpow,
      ``ManuscriptAudit.PrimeLocalizationUnits.exponent_unique] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
