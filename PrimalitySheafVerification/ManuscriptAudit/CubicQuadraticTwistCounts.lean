import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard

/-! Complementary point counts for actual centered quadratic twists. -/

namespace ManuscriptAudit.CubicQuadraticTwistCounts

open FiniteFieldPointCount CubicThreeTorsionCard

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

private def multiplyEquiv (d : K) (hd : d ≠ 0) : K ≃ K where
  toFun x := d * x
  invFun x := d⁻¹ * x
  left_inv x := by simp [← mul_assoc, hd]
  right_inv x := by simp [← mul_assoc, hd]

theorem quadratic_character_sum_neg {A d : K} (hd : ¬ IsSquare d) :
    (∑ x : K, quadraticChar K (x ^ 3 + d ^ 3 * A)) =
      -(∑ x : K, quadraticChar K (x ^ 3 + A)) := by
  have hd₀ : d ≠ 0 := fun h => hd (h.symm ▸ IsSquare.zero)
  have hχ : quadraticChar K d = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hd
  have hsum := Fintype.sum_equiv (multiplyEquiv d hd₀)
    (fun x => quadraticChar K ((d * x) ^ 3 + d ^ 3 * A))
    (fun x => quadraticChar K (x ^ 3 + d ^ 3 * A))
    (fun _ => rfl)
  rw [← hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [show (d * x) ^ 3 + d ^ 3 * A = d ^ 3 * (x ^ 3 + A) by ring]
  rw [map_mul, map_pow, hχ]
  ring

/-- The actual projective rational point counts of a centered cubic and a nonsquare twist
add up to twice the size of the projective line over the base field. -/
theorem projective_card_add {A d : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (hd : ¬ IsSquare d) :
    Nat.card (shortCubic (0 : K) A).toProjective.Point +
      Nat.card (shortCubic (0 : K) (d ^ 3 * A)).toProjective.Point =
        2 * (Fintype.card K + 1) := by
  have hd₀ : d ≠ 0 := fun h => hd (h.symm ▸ IsSquare.zero)
  have hchar : ringChar K ≠ 2 := by
    intro h
    exact h₂ (by simpa only [h, Nat.cast_ofNat] using (Nat.cast_ringChar (R := K)))
  have hB : d ^ 3 * A ≠ 0 := mul_ne_zero (pow_ne_zero _ hd₀) hA
  have hcA := shortCubic_projective_count_int hchar (shortCubic_discriminant_ne_zero h₂ h₃ hA)
  have hcB := shortCubic_projective_count_int hchar (shortCubic_discriminant_ne_zero h₂ h₃ hB)
  simp only [zero_mul, sub_zero, quadratic_character_sum_neg hd] at hcA hcB
  apply Int.ofNat_inj.mp
  push_cast
  rw [hcA, hcB]
  ring

end
end ManuscriptAudit.CubicQuadraticTwistCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicQuadraticTwistCounts.quadratic_character_sum_neg,
      ``ManuscriptAudit.CubicQuadraticTwistCounts.projective_card_add] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
