import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The principal-open coordinate rings inside K(t)

A nonempty principal open of the affine line has its actual coordinate
ring embedded in the rational function field. The normalized denominator
of any of its sections divides a power of the defining polynomial. For
a section which is a unit, the same holds for its numerator.
-/

namespace ManuscriptAudit.RatFuncPrincipalOpen

noncomputable section

variable (K : Type*) [Field K]

/-- The canonical ring map from the principal-open coordinate ring to the function field. -/
def toRatFunc (f : Polynomial K) (hf : f ≠ 0) : Localization.Away f →+* RatFunc K :=
  Localization.awayLift (algebraMap (Polynomial K) (RatFunc K)) f
    (isUnit_iff_ne_zero.mpr (RatFunc.algebraMap_ne_zero hf))

@[simp] theorem toRatFunc_algebraMap (f : Polynomial K) (hf : f ≠ 0) (p : Polynomial K) :
    toRatFunc K f hf (algebraMap (Polynomial K) (Localization.Away f) p) =
      algebraMap (Polynomial K) (RatFunc K) p :=
  IsLocalization.Away.lift_eq f (isUnit_iff_ne_zero.mpr (RatFunc.algebraMap_ne_zero hf)) p

theorem toRatFunc_injective (f : Polynomial K) (hf : f ≠ 0) :
    Function.Injective (toRatFunc K f hf) := by
  apply (injective_iff_map_eq_zero (toRatFunc K f hf)).2
  intro x hx
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj f x
  have hp' := congrArg (toRatFunc K f hf) hp
  simp only [map_mul, map_pow, toRatFunc_algebraMap, hx, zero_mul] at hp'
  have hz : p = 0 :=
    (RatFunc.algebraMap_injective K) (hp'.symm.trans (map_zero _).symm)
  rw [hz, map_zero] at hp
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away f) f n
  rw [← hu] at hp
  have h := congrArg (fun y : Localization.Away f => y * (↑(u⁻¹) : Localization.Away f)) hp
  simpa [mul_assoc] using h

/-- The actual map on units of the principal-open coordinate ring. -/
def unitMap (f : Polynomial K) (hf : f ≠ 0) :
    Additive (Localization.Away f)ˣ →+ Additive (RatFunc K)ˣ :=
  (Units.map (toRatFunc K f hf).toMonoidHom).toAdditive

theorem unitMap_injective (f : Polynomial K) (hf : f ≠ 0) :
    Function.Injective (unitMap K f hf) := by
  intro x y h
  apply Additive.ext
  apply Units.ext
  apply toRatFunc_injective K f hf
  exact congrArg (fun u : Additive (RatFunc K)ˣ => (u.toMul : RatFunc K)) h

/-- The canonical rational function representation of a principal-open section
has denominators supported on the omitted closed points. -/
theorem denom_dvd_pow (f : Polynomial K) (hf : f ≠ 0) (x : Localization.Away f) :
    ∃ n : ℕ, (toRatFunc K f hf x).denom ∣ f ^ n := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj f x
  have hp' := congrArg (toRatFunc K f hf) hp
  simp only [map_mul, map_pow, toRatFunc_algebraMap] at hp'
  let a := algebraMap (Polynomial K) (RatFunc K)
  have hq : a (f ^ n) ≠ 0 := RatFunc.algebraMap_ne_zero (pow_ne_zero n hf)
  have h : toRatFunc K f hf x = a p / a (f ^ n) := by
    apply (eq_div_iff hq).2
    simpa only [map_pow] using hp'
  exact ⟨n, by rw [h]; exact RatFunc.denom_div_dvd _ _⟩

/-- The ring embedding carries the inverse of a local unit to its field inverse. -/
theorem toRatFunc_unit_inv (f : Polynomial K) (hf : f ≠ 0) (x : (Localization.Away f)ˣ) :
    toRatFunc K f hf (↑(x⁻¹) : Localization.Away f) =
      (toRatFunc K f hf (x : Localization.Away f))⁻¹ := by
  let u := Units.map (toRatFunc K f hf).toMonoidHom x
  change (↑(u⁻¹) : RatFunc K) = (u : RatFunc K)⁻¹
  apply mul_left_cancel₀ u.ne_zero
  exact u.mul_inv.trans (mul_inv_cancel₀ u.ne_zero).symm

/-- The numerator of a unit section also has its roots outside the principal open. -/
theorem num_dvd_pow_of_isUnit (f : Polynomial K) (hf : f ≠ 0) (x : (Localization.Away f)ˣ) :
    ∃ n : ℕ, (toRatFunc K f hf (x : Localization.Away f)).num ∣ f ^ n := by
  let u := Units.map (toRatFunc K f hf).toMonoidHom x
  obtain ⟨n, hn⟩ := denom_dvd_pow K f hf (↑(x⁻¹) : Localization.Away f)
  rw [toRatFunc_unit_inv] at hn
  exact ⟨n, (RatFunc.associated_denom_inv u.ne_zero).symm.dvd.trans hn⟩

end

end ManuscriptAudit.RatFuncPrincipalOpen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RatFuncPrincipalOpen.toRatFunc_injective,
      ``ManuscriptAudit.RatFuncPrincipalOpen.unitMap_injective,
      ``ManuscriptAudit.RatFuncPrincipalOpen.denom_dvd_pow,
      ``ManuscriptAudit.RatFuncPrincipalOpen.num_dvd_pow_of_isUnit] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
