import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.AppellNumerator
import PrimalitySheafVerification.ManuscriptAudit.AppellSameIntegerShift

/-!
# The actual three half-period blocks of Paper 8

The first block has the verified vanishing bilateral numerator.
The integer-shifted block is the same Appell function. The half-shifted
block on τ is the initial Appell numerator on τ+1, since the numerator
is periodic in τ at fixed elliptic arguments.
-/

namespace ManuscriptAudit.AppellHalfBlocks

open AppellLerchBase AppellSameIntegerShift

noncomputable section

private abbrev phase (z : ℂ) := (Real.pi : ℂ) * Complex.I * z

private theorem exp_add_phase (a b : ℂ) :
    Complex.exp (phase (a + b)) = Complex.exp (phase a) * Complex.exp (phase b) := by
  change Complex.exp (((Real.pi : ℂ) * Complex.I) * (a + b)) = _
  rw [mul_add, Complex.exp_add]

private theorem exp_phase_int (n : ℤ) :
    Complex.exp (phase (n : ℂ)) = (-1 : ℂ) ^ n := by
  have h : phase (n : ℂ) = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]

private theorem exp_phase_two_int (n : ℤ) :
    Complex.exp (phase (2 * (n : ℂ))) = 1 := by
  have h : phase (2 * (n : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private theorem exp_phase_zpow (τ : ℂ) (n : ℤ) :
    Complex.exp (phase ((n : ℂ) * τ)) = Complex.exp (phase τ) ^ n := by
  have h : phase ((n : ℂ) * τ) = (n : ℂ) * phase τ := by ring
  rw [h, Complex.exp_int_mul]

theorem numeratorTerm_base_eq (τ : ℂ) (n : ℤ) :
    numeratorTerm (τ / 2) (τ / 2 + 1 / 2) τ n =
      appellTerm (Complex.exp (phase τ)) n := by
  have hn : ((n : ℂ) ^ 2 + n) * τ + 2 * (n : ℂ) * (τ / 2 + 1 / 2) =
      ((n * (n + 2) : ℤ) : ℂ) * τ + (n : ℂ) := by
    push_cast
    ring
  have hd : 2 * (τ / 2 + (n : ℂ) * τ) = ((2 * n + 1 : ℤ) : ℂ) * τ := by
    push_cast
    ring
  have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_zpow]
    simp
  unfold numeratorTerm appellTerm
  rw [hn, hd, exp_add_phase, exp_phase_int, exp_phase_zpow, exp_phase_zpow]
  congr 1
  calc
    _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * Complex.exp (phase τ) ^ (n * (n + 2)) := by ring
    _ = _ := by rw [hs, one_mul]

/-- The genuine signed bilateral numerator at the initial block has sum zero. -/
theorem baseBlock_numerator_hasSum (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (numeratorTerm (τ / 2) (τ / 2 + 1 / 2) τ) 0 := by
  have h : numeratorTerm (τ / 2) (τ / 2 + 1 / 2) τ =
      appellTerm (Complex.exp (phase τ)) := funext (numeratorTerm_base_eq τ)
  rw [h]
  exact hasSum_appellTerm_halfNome_zero τ hτ

private theorem product_two_dvd (n : ℤ) : 2 ∣ n * (n + 1) := by
  have h : n % 2 = 0 ∨ (n + 1) % 2 = 0 := by omega
  rcases h with h | h
  · exact dvd_mul_of_dvd_left (show (2 : ℤ) ∣ n by omega) _
  · exact dvd_mul_of_dvd_right (show (2 : ℤ) ∣ n + 1 by omega) _

theorem numeratorTerm_tau_add_one (u v τ : ℂ) (n : ℤ) :
    numeratorTerm u v (τ + 1) n = numeratorTerm u v τ n := by
  obtain ⟨m, hm⟩ := product_two_dvd n
  have hnc : (n : ℂ) ^ 2 + n = 2 * (m : ℂ) := by
    have h : ((n * (n + 1) : ℤ) : ℂ) = ((2 * m : ℤ) : ℂ) := congrArg Int.cast hm
    push_cast at h
    linear_combination h
  have hNum : ((n : ℂ) ^ 2 + n) * (τ + 1) + 2 * (n : ℂ) * v =
      ((n : ℂ) ^ 2 + n) * τ + 2 * (n : ℂ) * v + 2 * (m : ℂ) := by
    rw [← hnc]
    ring
  have hDen : 2 * (u + (n : ℂ) * (τ + 1)) =
      2 * (u + (n : ℂ) * τ) + 2 * (n : ℂ) := by ring
  unfold numeratorTerm
  rw [hNum, hDen, exp_add_phase (((n : ℂ) ^ 2 + n) * τ + 2 * (n : ℂ) * v)
    (2 * (m : ℂ)), exp_add_phase (2 * (u + (n : ℂ) * τ)) (2 * (n : ℂ)),
    exp_phase_two_int m, exp_phase_two_int n, mul_one, mul_one]

/-- The genuine signed bilateral numerator at the half-shifted block has sum zero. -/
theorem halfBlock_numerator_hasSum (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (numeratorTerm (τ / 2 + 1 / 2) (τ / 2 + 1) τ) 0 := by
  have hu : (τ + 1) / 2 = τ / 2 + 1 / 2 := by ring
  have hv : (τ + 1) / 2 + 1 / 2 = τ / 2 + 1 := by ring
  have hi : (τ + 1).im = τ.im := by simp
  have h := baseBlock_numerator_hasSum (τ + 1) (by rw [hi]; exact hτ)
  rw [hu, hv] at h
  simpa only [numeratorTerm_tau_add_one] using h

/-- All three displayed Paper 8 blocks have zero Appell value on the upper half-plane. -/
theorem paper8_displayed_three_blocks_zero (τ : ℂ) (hτ : 0 < τ.im) :
    mu (τ / 2) (τ / 2 + 1 / 2) τ = 0 ∧
    mu (τ / 2 + τ) (τ / 2 + 1 / 2 + τ) τ = 0 ∧
    mu (τ / 2 + 1 / 2) (τ / 2 + 1) τ = 0 := by
  have h₀ : mu (τ / 2) (τ / 2 + 1 / 2) τ = 0 := by
    unfold mu numerator
    rw [(baseBlock_numerator_hasSum τ hτ).tsum_eq, mul_zero, zero_div]
  have h₁ : mu (τ / 2 + τ) (τ / 2 + 1 / 2 + τ) τ = 0 :=
    (mu_simultaneous_shift _ _ _).trans h₀
  have h₂ : mu (τ / 2 + 1 / 2) (τ / 2 + 1) τ = 0 := by
    unfold mu numerator
    rw [(halfBlock_numerator_hasSum τ hτ).tsum_eq, mul_zero, zero_div]
  exact ⟨h₀, h₁, h₂⟩

end

end ManuscriptAudit.AppellHalfBlocks

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.AppellHalfBlocks.baseBlock_numerator_hasSum,
      ``ManuscriptAudit.AppellHalfBlocks.numeratorTerm_tau_add_one,
      ``ManuscriptAudit.AppellHalfBlocks.halfBlock_numerator_hasSum,
      ``ManuscriptAudit.AppellHalfBlocks.paper8_displayed_three_blocks_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
