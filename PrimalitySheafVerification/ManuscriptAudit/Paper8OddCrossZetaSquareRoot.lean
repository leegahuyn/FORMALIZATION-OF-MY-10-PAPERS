import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.Convolution
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossSquareRoot
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossZetaFactorization

/-! Absolute convergence of the genuine cross zeta series in the half-plane Re(s) > 3/4. -/

namespace ManuscriptAudit.Paper8OddCrossZetaSquareRoot

open Finset Paper8OddCrossSquareRoot Paper8OddCrossCuspCutoff Paper8OddCrossZetaFactorization
open scoped LSeries.notation

noncomputable section

theorem two_pow_primeFactors_card_le_divisors_card {k : ℕ} (hk : k ≠ 0) :
    2 ^ k.primeFactors.card ≤ k.divisors.card := by
  rw [Nat.card_divisors hk]
  calc
    _ = ∏ _p ∈ k.primeFactors, (2 : ℕ) := by rw [Finset.prod_const]
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro p hp
      have hP := Nat.prime_of_mem_primeFactors hp
      have he := hP.factorization_pos_of_dvd hk (Nat.dvd_of_mem_primeFactors hp)
      omega

theorem divisor_count_dirichlet_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun j : ℕ => ((j + 1).divisors.card : ℝ) / ((j + 1 : ℕ) : ℝ) ^ t) := by
  let f : ℕ → ℂ := fun _ => 1
  have hOne : LSeriesSummable f (t : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_real (m := 1) (fun _ _ => by simp [f]) ht
  have hConv : Summable (LSeries.term (f ⍟ f) (t : ℂ)) := hOne.convolution hOne
  have hCard (k : ℕ) : (f ⍟ f) k = (k.divisors.card : ℂ) := by
    rw [LSeries.convolution_def]
    change (∑ p ∈ k.divisorsAntidiagonal, f p.1 * f p.2) = _
    rw [Nat.sum_divisorsAntidiagonal (fun a b => f a * f b)]
    simp [f]
  have hS : Summable (fun j : ℕ => ‖LSeries.term (f ⍟ f) (t : ℂ) (j + 1)‖) :=
    (summable_nat_add_iff 1).2 hConv.norm
  refine hS.congr (fun j => ?_)
  rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero j), hCard, Complex.norm_natCast, Complex.ofReal_re]

theorem norm_oddCrossZetaTerm_le_divisors (s : ℂ) (j : ℕ) :
    ‖oddCrossZetaTerm s j‖ ≤
      (2 : ℝ) ^ (-2 * s.re) * (((j + 1).divisors.card : ℝ) /
        ((j + 1 : ℕ) : ℝ) ^ (2 * s.re - 1 / 2)) := by
  let k := j + 1
  have hk : 0 < k := Nat.succ_pos j
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hCard : (2 : ℝ) ^ k.primeFactors.card ≤ (k.divisors.card : ℝ) := by
    exact_mod_cast two_pow_primeFactors_card_le_divisors_card hk.ne'
  have hArithmetic : ‖crossSum hk‖ ≤ (k.divisors.card : ℝ) * Real.sqrt (k : ℝ) :=
    (norm_crossSum_squareRoot hk).trans (mul_le_mul_of_nonneg_right hCard (Real.sqrt_nonneg _))
  unfold oddCrossZetaTerm
  change ‖crossSum hk * crossModulusFactor s (2 * (k : ℝ))‖ ≤ _
  rw [norm_mul, crossModulusFactor_norm s (by positivity),
    Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hkR.le]
  calc
    _ ≤ (k.divisors.card : ℝ) * Real.sqrt (k : ℝ) *
        ((2 : ℝ) ^ (-2 * s.re) * (k : ℝ) ^ (-2 * s.re)) :=
      mul_le_mul_of_nonneg_right hArithmetic (by positivity)
    _ = _ := by
      change _ = (2 : ℝ) ^ (-2 * s.re) * ((k.divisors.card : ℝ) / (k : ℝ) ^ (2 * s.re - 1 / 2))
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hkR.le,
        show -(2 * s.re - 1 / 2) = (1 / 2 : ℝ) + (-2 * s.re) by ring, Real.rpow_add hkR]
      ring

theorem oddCrossZetaTerm_abs_summable_threeQuarter (s : ℂ) (hs : (3 / 4 : ℝ) < s.re) :
    Summable (fun j : ℕ => ‖oddCrossZetaTerm s j‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_oddCrossZetaTerm_le_divisors s)
    ((divisor_count_dirichlet_summable (show 1 < 2 * s.re - 1 / 2 by linarith)).mul_left _)

end
end ManuscriptAudit.Paper8OddCrossZetaSquareRoot

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossZetaSquareRoot.divisor_count_dirichlet_summable,
      ``ManuscriptAudit.Paper8OddCrossZetaSquareRoot.oddCrossZetaTerm_abs_summable_threeQuarter] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
