import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProductStationaryPhase

/-! Exact multiplicity when reducing units through a product modulus with the same prime divisors. -/

namespace ManuscriptAudit.Paper8UnitReductionThree

open Finset Paper8ProductStationaryPhase Paper8ZModDigitOrthogonality
open scoped Classical

noncomputable section

theorem sum_units_as_indicator {n : ℕ} [NeZero n] (F : ZMod n → ℂ) :
    (∑ x : (ZMod n)ˣ, F x) = ∑ x : ZMod n, if IsUnit x then F x else 0 := by
  let e : (ZMod n)ˣ ≃ {x : ZMod n // IsUnit x} :=
    { toFun := fun x => ⟨x, x.isUnit⟩
      invFun := fun x => x.2.unit
      left_inv := fun x => Units.ext x.isUnit.unit_spec
      right_inv := fun x => Subtype.ext x.2.unit_spec }
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x : ZMod n => IsUnit x) _ (by simp)]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem isUnit_mul_iff_reduceLow {n k : ℕ} [NeZero n] [NeZero k]
    (hBoth : ∀ a : ℕ, a.Coprime k → a.Coprime n) (x : ZMod (n * k)) :
    IsUnit x ↔ IsUnit (reduceLowDigit x : ZMod k) := by
  obtain ⟨a, rfl⟩ := (show Function.Surjective (Nat.cast : ℕ → ZMod (n * k)) from fun x =>
    ⟨x.val, ZMod.natCast_zmod_val x⟩) x
  rw [map_natCast, ZMod.isUnit_iff_coprime, ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
  exact ⟨And.right, fun h => ⟨hBoth a h, h⟩⟩

theorem sum_units_mul_lifts {n k : ℕ} [NeZero n] [NeZero k]
    (hBoth : ∀ a : ℕ, a.Coprime k → a.Coprime n) (F : ZMod k → ℂ) :
    (∑ x : (ZMod (n * k))ˣ, F (reduceLowDigit (x : ZMod (n * k)))) =
      (n : ℂ) * ∑ x : (ZMod k)ˣ, F x := by
  rw [sum_units_as_indicator (fun x : ZMod (n * k) => F (reduceLowDigit x)),
    sum_units_as_indicator F, sum_residue_digits]
  have hReduced (a : ZMod n) (b : ZMod k) :
      (reduceLowDigit ((b.val + k * a.val : ℕ) : ZMod (n * k)) : ZMod k) = b := by
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
  simp_rw [isUnit_mul_iff_reduceLow hBoth, hReduced]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]

theorem isUnit_three_mul_iff_reduceLow {k : ℕ} [NeZero k] (h3 : 3 ∣ k) (x : ZMod (3 * k)) :
    IsUnit x ↔ IsUnit (reduceLowDigit x : ZMod k) :=
  isUnit_mul_iff_reduceLow (fun _ h => Nat.Coprime.of_dvd_right h3 h) x

theorem sum_units_three_lifts {k : ℕ} [NeZero k] (h3 : 3 ∣ k) (F : ZMod k → ℂ) :
    (∑ x : (ZMod (3 * k))ˣ, F (reduceLowDigit (x : ZMod (3 * k)))) =
      3 * ∑ x : (ZMod k)ˣ, F x := by
  simpa only [Nat.cast_ofNat] using
    sum_units_mul_lifts (n := 3) (fun _ h => Nat.Coprime.of_dvd_right h3 h) F

end
end ManuscriptAudit.Paper8UnitReductionThree

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8UnitReductionThree.sum_units_three_lifts
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
