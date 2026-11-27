import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadow

/-! The bilateral theta on p. 332 is twice the positive-index theta on p. 338. -/

namespace ManuscriptAudit.Paper8BilateralKroneckerShadow

open Paper8ExteriorNormalization (kroneckerNegTwelve)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8KroneckerShadow

noncomputable section

def bilateralTerm (τ : ℂ) (n : ℤ) : ℂ :=
  (kroneckerNegTwelve n : ℂ) * (n : ℂ) * Complex.exp (periodCoefficient * (n : ℂ) ^ 2 * τ / 24)

def bilateralShadow (τ : ℂ) : ℂ := ∑' n : ℤ, bilateralTerm τ n

theorem kronecker_at_neg (n : ℤ) : kroneckerNegTwelve (-n) = -kroneckerNegTwelve n := by
  by_cases hEven : n % 2 = 0
  · have hMinus : (-n) % 2 = 0 := by omega
    simp [kroneckerNegTwelve, hEven, hMinus]
  have hMinus : (-n) % 2 ≠ 0 := by omega
  by_cases hNeg : n < 0
  · have hPos : ¬ -n < 0 := by omega
    simp [kroneckerNegTwelve, hEven, hMinus, hNeg, hPos, Int.natAbs_neg]
  · have hn : n ≠ 0 := by
      intro h
      subst n
      simp at hEven
    have hNegMinus : -n < 0 := by omega
    simp [kroneckerNegTwelve, hEven, hMinus, hNeg, hNegMinus, Int.natAbs_neg]

theorem bilateralTerm_even (τ : ℂ) (n : ℤ) : bilateralTerm τ (-n) = bilateralTerm τ n := by
  simp only [bilateralTerm, kronecker_at_neg, Int.cast_neg, neg_mul_neg, neg_sq]

private theorem bilateralTerm_zero (τ : ℂ) : bilateralTerm τ 0 = 0 := by
  simp [bilateralTerm]

private theorem bilateralTerm_nat (τ : ℂ) (n : ℕ) :
    bilateralTerm τ (n : ℤ) = shadowTerm n (rootParameter τ) := by
  rw [shadowTerm_root_eq_exponential]
  simp only [bilateralTerm, coefficient, Int.cast_natCast]

theorem bilateral_absolute_summability {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖bilateralTerm τ n‖) := by
  have hNat : Summable (fun n : ℕ => ‖bilateralTerm τ (n : ℤ)‖) := by
    simpa only [bilateralTerm_nat] using shadowSeries_absolute_summability (rootParameter_norm_lt_one hτ)
  exact Summable.of_nat_of_neg hNat (by simpa only [bilateralTerm_even] using hNat)

theorem bilateral_eq_two_unary {τ : ℂ} (hτ : 0 < τ.im) :
    bilateralShadow τ = 2 * unaryShadow τ := by
  have hNat : Summable (fun n : ℕ => bilateralTerm τ (n : ℤ)) := by
    simpa only [bilateralTerm_nat] using
      (shadowSeries_absolute_summability (rootParameter_norm_lt_one hτ)).of_norm
  have hNeg : Summable (fun n : ℕ => bilateralTerm τ (-(n : ℤ))) :=
    by simpa only [bilateralTerm_even] using hNat
  simpa only [bilateralShadow, bilateralTerm_even, bilateralTerm_nat, bilateralTerm_zero,
    unaryShadow, shadowSeries, sub_zero, two_mul] using hNat.tsum_of_nat_of_neg hNeg

end
end ManuscriptAudit.Paper8BilateralKroneckerShadow

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8BilateralKroneckerShadow.kronecker_at_neg,
      ``ManuscriptAudit.Paper8BilateralKroneckerShadow.bilateralTerm_even,
      ``ManuscriptAudit.Paper8BilateralKroneckerShadow.bilateral_absolute_summability,
      ``ManuscriptAudit.Paper8BilateralKroneckerShadow.bilateral_eq_two_unary] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
