import Lean.Util.CollectAxioms
import Mathlib.Tactic.IntervalCases
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadow

/-! The literal pp. 332 and 338 unary theta has phase exp(πi/12) under unit translation. -/

namespace ManuscriptAudit.Paper8KroneckerShadowPhase

open Paper8ExteriorNormalization (kroneckerNegTwelve)
open Paper8HolomorphicPartPhase (periodCoefficient qParameter normalizationPhase)
open Paper8KroneckerShadow

noncomputable section

def shadowPhase : ℂ := Complex.exp (periodCoefficient / 24)

private theorem square_mod_twentyFour {n : ℕ} (hOdd : n % 2 = 1) (hThree : ¬ 3 ∣ n) :
    n ^ 2 % 24 = 1 := by
  have hMod : n ^ 2 % 24 = ((n % 24) ^ 2) % 24 := by
    simpa only [pow_two] using Nat.mul_mod n n 24
  have h2 : (n % 24) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 24)]
    exact hOdd
  have h3 : (n % 24) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 24)]
    exact fun h => hThree (Nat.dvd_of_mod_eq_zero h)
  rw [hMod]
  have hBound := Nat.mod_lt n (by decide : 0 < 24)
  interval_cases hR : n % 24 <;> norm_num [hR] at *

theorem coefficient_square_mod_twentyFour {n : ℕ} (hc : coefficient n ≠ 0) :
    n ^ 2 % 24 = 1 := by
  have hN : n ≠ 0 := by
    intro h
    subst n
    simp [coefficient] at hc
  have hChi : kroneckerNegTwelve (n : ℤ) ≠ 0 := by
    intro h
    simp [coefficient, h] at hc
  have hOddInt : (n : ℤ) % 2 ≠ 0 := by
    intro h
    exact hChi (by simp [kroneckerNegTwelve, h])
  have hOdd : n % 2 = 1 := by omega
  have hNonneg : ¬ (n : ℤ) < 0 := by omega
  have hJac : jacobiSym (-12) n ≠ 0 := by
    intro h
    exact hChi (by simp [kroneckerNegTwelve, hOddInt, hNonneg, h])
  refine square_mod_twentyFour hOdd ?_
  intro hDiv
  apply hJac (jacobiSym.eq_zero_iff.mpr ⟨hN, ?_⟩)
  rw [Int.gcd_eq_natAbs]
  intro hEq
  have hD : 3 ∣ Nat.gcd 12 n := Nat.dvd_gcd (by decide) hDiv
  have hEq' : Nat.gcd 12 n = 1 := by simpa using hEq
  rw [hEq'] at hD
  exact (by decide : ¬ (3 : ℕ) ∣ 1) hD

theorem rootParameter_add_one (τ : ℂ) :
    rootParameter (τ + 1) = shadowPhase * rootParameter τ := by
  rw [rootParameter, rootParameter, shadowPhase, mul_add, mul_one, Complex.exp_add]
  exact mul_comm _ _

theorem shadowPhase_pow_twentyFour : shadowPhase ^ (24 : ℕ) = 1 := by
  have hRoot := rootParameter_pow (1 : ℂ)
  simpa only [rootParameter, shadowPhase, qParameter, mul_one, periodCoefficient,
    Complex.exp_two_pi_mul_I] using hRoot

theorem shadowPhase_eq_inverse_normalization : shadowPhase = normalizationPhase⁻¹ := by
  rw [shadowPhase, normalizationPhase, Complex.exp_neg, inv_inv]

theorem unaryShadow_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    unaryShadow (τ + 1) = shadowPhase * unaryShadow τ := by
  have hTerm (n : ℕ) :
      shadowTerm n (rootParameter (τ + 1)) = shadowPhase * shadowTerm n (rootParameter τ) := by
    by_cases h : coefficient n = 0
    · simp [shadowTerm, h]
    · have hResidue := coefficient_square_mod_twentyFour h
      have hEq : n ^ 2 = 24 * (n ^ 2 / 24) + 1 := by
        have hd := Nat.mod_add_div (n ^ 2) 24
        omega
      have hPow : shadowPhase ^ (n ^ 2) = shadowPhase := by
        rw [hEq, pow_succ, pow_mul, shadowPhase_pow_twentyFour, one_pow, one_mul]
      rw [shadowTerm, shadowTerm, rootParameter_add_one, mul_pow, hPow]
      ring
  unfold unaryShadow shadowSeries
  simp_rw [hTerm]
  exact (shadowSeries_absolute_summability (rootParameter_norm_lt_one hτ)).of_norm.tsum_mul_left _

end
end ManuscriptAudit.Paper8KroneckerShadowPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8KroneckerShadowPhase.coefficient_square_mod_twentyFour,
      ``ManuscriptAudit.Paper8KroneckerShadowPhase.shadowPhase_pow_twentyFour,
      ``ManuscriptAudit.Paper8KroneckerShadowPhase.shadowPhase_eq_inverse_normalization,
      ``ManuscriptAudit.Paper8KroneckerShadowPhase.unaryShadow_add_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
