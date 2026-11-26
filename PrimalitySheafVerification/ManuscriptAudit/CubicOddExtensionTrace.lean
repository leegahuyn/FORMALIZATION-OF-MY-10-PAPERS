import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiRoots

/-! Actual point counts over every odd-degree extension at primes p congruent to 2 mod 3. -/

namespace ManuscriptAudit.CubicOddExtensionTrace

open CubicHasseBound CubicJacobiRoots FiniteFieldPointCount

noncomputable section

variable {p : ℕ} [Fact p.Prime]
  {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

private theorem power_mod_three (hp : p % 3 = 2) {d : ℕ} (hd : Odd d) :
    p ^ d ≡ 2 [MOD 3] := by
  have hp' : p ≡ 2 [MOD 3] := by simpa [Nat.ModEq] using hp
  have he : 2 ^ d ≡ 2 [MOD 3] := by
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_add, pow_mul, pow_one]
    change 4 ^ k * 2 ≡ 2 [MOD 3]
    simpa only [one_pow, one_mul] using
      ((by decide : 4 ≡ 1 [MOD 3]).pow k).mul (Nat.ModEq.refl 2)
  exact (hp'.pow d).trans he

theorem odd_extension_card_mod_three (hp : p % 3 = 2)
    (hd : Odd (Module.finrank (ZMod p) E)) :
    Fintype.card E % 3 = 2 := by
  have hc : Fintype.card E = p ^ Module.finrank (ZMod p) E := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank, Nat.card_eq_fintype_card,
      ZMod.card]
  rw [hc]
  simpa [Nat.ModEq] using power_mod_three hp hd

/-- The actual curve has exactly one more point than the extension's field size. -/
theorem odd_extension_projective_count (hp : p % 3 = 2)
    (hd : Odd (Module.finrank (ZMod p) E)) (hE : ringChar E ≠ 2)
    {A : E} (hΔ : (shortCubic (0 : E) A).Δ ≠ 0) :
    Nat.card (shortCubic (0 : E) A).toProjective.Point = Fintype.card E + 1 := by
  have hc := odd_extension_card_mod_three (E := E) hp hd
  have hdiv : ¬ 3 ∣ Fintype.card E - 1 := by
    have hpos : 0 < Fintype.card E := Fintype.card_pos
    intro h
    rw [Nat.dvd_iff_mod_eq_zero] at h
    omega
  have h := projective_count_trace_complex hE hΔ
  rw [trace_zero_of_no_orderThree hE hdiv A, neg_zero, sub_eq_zero] at h
  exact_mod_cast h.symm

end
end ManuscriptAudit.CubicOddExtensionTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicOddExtensionTrace.odd_extension_card_mod_three,
      ``ManuscriptAudit.CubicOddExtensionTrace.odd_extension_projective_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
