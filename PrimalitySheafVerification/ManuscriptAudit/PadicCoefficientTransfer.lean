import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Binomial
import PrimalitySheafVerification.ManuscriptAudit.PadicExactBridge
import PrimalitySheafVerification.ManuscriptAudit.PadicLipschitz
import PrimalitySheafVerification.ManuscriptAudit.PadicLogNonzero
import PrimalitySheafVerification.ManuscriptAudit.PadicRemainder

/-!
# The Paper 1 coefficient sum at the stated precision

The expansion printed as (2) has the opposite sign to the normalized
discrepancy. The printed congruence still holds at the stated modulus.
At the finer precision available for odd primes, the negative sign
is visible in the error bound.
-/

namespace ManuscriptAudit.PadicCoefficientTransfer

open scoped BigOperators
open Spt1.PadicLog
open PadicLogNonzero

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- The unnormalized coefficient that multiplies the integer `aⱼ` in (2). -/
def coefficient (m : ℕ) (M : ℚ_[p]) (S : ℕ → ℚ_[p]) (j : ℕ) : ℚ_[p] :=
  M * S j / (Nat.gcd j.factorial m : ℚ_[p])

theorem coefficient_div_eq_printed (m : ℕ) (M Y : ℚ_[p]) (S : ℕ → ℚ_[p]) (j : ℕ) :
    coefficient m M S j / Y = M * S j / ((Nat.gcd j.factorial m : ℚ_[p]) * Y) := by
  rw [coefficient, div_div]

theorem coefficient_mul_eq_printed (m : ℕ) (M : ℚ_[p]) (S : ℕ → ℚ_[p]) (a : ℤ) (j : ℕ) :
    (a : ℚ_[p]) * coefficient m M S j = ((a : ℚ_[p]) / (Nat.gcd j.factorial m : ℚ_[p])) * M * S j := by
  simp only [coefficient, div_eq_mul_inv]
  ring

/-- The manuscript's shifted binomial basis on arbitrary integer bases. -/
def shiftedBinomial (A : ℤ) (j : ℕ) : ℤ :=
  Ring.choose (A + 1) j

theorem shiftedBinomial_cast (A : ℤ) (j : ℕ) :
    (shiftedBinomial A j : ℚ_[p]) = Ring.choose ((A : ℚ_[p]) + 1) j := by
  have h := Ring.map_choose (Int.castRingHom ℚ_[p]) (A + 1) j
  change (Ring.choose (A + 1) j : ℚ_[p]) = Ring.choose ((A + 1 : ℤ) : ℚ_[p]) j at h
  simpa only [shiftedBinomial, Int.cast_add, Int.cast_one] using h

theorem shiftedBinomial_padic_norm_le_one (A : ℤ) (j : ℕ) :
    ‖Ring.choose ((A : ℚ_[p]) + 1) j‖ ≤ 1 := by
  rw [← shiftedBinomial_cast]
  exact Padic.norm_int_le_one _

private theorem valuation_div {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x / y).valuation = x.valuation - y.valuation := by
  rw [div_eq_mul_inv, Padic.valuation_mul hx (inv_ne_zero hy), Padic.valuation_inv,
    sub_eq_add_neg]

/-- The p. 8 valuation identity with its actual factorial gcd and shifted
binomial. Nonzero arguments use the usual finite additive valuation. -/
theorem paper1_printed_coefficient_valuation
    (m q j : ℕ) {A M : ℤ} (hA : A ≠ 0) (hM : M ≠ 0)
    (hS : shiftedBinomial A j ≠ 0) :
    (((M : ℚ_[p]) * (shiftedBinomial A j : ℚ_[p]) /
      (Nat.gcd j.factorial m : ℚ_[p])) / (A : ℚ_[p]) ^ q).valuation =
      (M : ℚ_[p]).valuation + (shiftedBinomial A j : ℚ_[p]).valuation
        - (Nat.gcd j.factorial m : ℚ_[p]).valuation - (q : ℤ) * (A : ℚ_[p]).valuation := by
  have hA' : (A : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hA
  have hM' : (M : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hM
  have hS' : (shiftedBinomial A j : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hS
  have hG : (Nat.gcd j.factorial m : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left _ (Nat.factorial_pos j)).ne'
  rw [valuation_div (div_ne_zero (mul_ne_zero hM' hS') hG) (pow_ne_zero _ hA'),
    valuation_div (mul_ne_zero hM' hS') hG, Padic.valuation_mul hM' hS', Padic.valuation_pow]

/-- The ordinary ultrametric estimate with a genuine prime power in
the modulus. The indexed prime version has a different norm factor. -/
theorem paper1_power_modulus_norm_upper_bounds (n : ℕ) (A y : ℚ_[p]) :
    ‖(p : ℚ_[p]) ^ n * y + (A - 1)‖ ≤
      max ((p : ℝ) ^ (-(n : ℤ)) * ‖y‖) ‖A - 1‖ ∧
    ‖(p : ℚ_[p]) ^ n * y - (A - 1)‖ ≤
      max ((p : ℝ) ^ (-(n : ℤ)) * ‖y‖) ‖A - 1‖ := by
  have hNorm : ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-(n : ℤ)) := by
    simpa only [zpow_natCast] using Padic.norm_p_zpow (p := p) (n : ℤ)
  constructor
  · simpa only [norm_mul, hNorm] using
      IsUltrametricDist.norm_add_le_max ((p : ℚ_[p]) ^ n * y) (A - 1)
  · simpa only [sub_eq_add_neg, norm_neg, norm_mul, hNorm] using
      IsUltrametricDist.norm_add_le_max ((p : ℚ_[p]) ^ n * y) (-(A - 1))

theorem padic_norm_bound_of_valuation_threshold (x : ℚ_[p]) (k : ℕ)
    (h : (k : ℤ) ≤ x.valuation) : ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  by_cases hx : x = 0
  · rw [hx, norm_zero]
    exact zpow_nonneg (zero_le_one.trans hp.le) _
  · rw [Padic.norm_eq_zpow_neg_valuation hx]
    apply zpow_le_zpow_right₀ hp.le
    exact neg_le_neg h

/-- The norm congruence is exactly divisibility by p^k with a p-adic
integer quotient. This uses the p-adic integer ball inside Q_p. -/
theorem padic_norm_bound_iff_prime_power_integral_multiple (x : ℚ_[p]) (k : ℕ) :
    ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ)) ↔
      ∃ z : ℤ_[p], x = (p : ℚ_[p]) ^ k * (z : ℚ_[p]) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpK : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ hp
  have hNorm : ‖(p : ℚ_[p]) ^ k‖ = (p : ℝ) ^ (-(k : ℤ)) := by
    simpa only [zpow_natCast] using Padic.norm_p_zpow (p := p) (k : ℤ)
  rw [← hNorm]
  constructor
  · intro hx
    have hInt : ‖x / (p : ℚ_[p]) ^ k‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one₀ (norm_pos_iff.mpr hpK)).2 hx
    refine ⟨⟨x / (p : ℚ_[p]) ^ k, hInt⟩, ?_⟩
    change x = (p : ℚ_[p]) ^ k * (x / (p : ℚ_[p]) ^ k)
    field_simp [hpK] <;> ring
  · rintro ⟨z, rfl⟩
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) z.property

private theorem norm_sum_le {f : ℕ → ℚ_[p]} {R : ℝ} (hR : 0 ≤ R) (n : ℕ)
    (hf : ∀ j < n, ‖f j‖ ≤ R) : ‖∑ j ∈ Finset.range n, f j‖ ≤ R := by
  induction n with
  | zero => simpa using hR
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (ih fun j hj => hf j (Nat.lt_succ_of_lt hj)) (hf n (Nat.lt_succ_self n)))

theorem paper1_coefficient_transfer
    (n q m k : ℕ) (hk : 1 ≤ k) {A X M : ℚ_[p]}
    (hA : A ≠ 0) (a : ℕ → ℤ) (S : ℕ → ℚ_[p])
    (hExp : A ^ q = X + ∑ j ∈ Finset.range n, (a j : ℚ_[p]) * coefficient m M S j)
    (hVal : ∀ j < n, ‖coefficient m M S j / A ^ q‖ ≤ (p : ℝ) ^ (-(k : ℤ))) :
    let W := ∑ j ∈ Finset.range n, (a j : ℚ_[p]) * (coefficient m M S j / A ^ q)
    let D := padicLog p X - (q : ℚ_[p]) * padicLog p A
    let R := (p : ℝ) ^ (-(k : ℤ))
    (X - A ^ q) / A ^ q = -W ∧ D = padicLog1p (-W) ∧
      ‖D‖ ≤ R ∧ ‖W - D‖ ≤ R ∧
      (3 ≤ p → ‖D + W‖ ≤ (p : ℝ) ^ (-(2 * (k : ℤ)))) := by
  dsimp only
  set W := ∑ j ∈ Finset.range n, (a j : ℚ_[p]) * (coefficient m M S j / A ^ q)
  set D := padicLog p X - (q : ℚ_[p]) * padicLog p A
  set R := (p : ℝ) ^ (-(k : ℤ))
  have hp : p.Prime := Fact.out
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpRpos : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hR : 0 ≤ R := zpow_nonneg hpRpos.le _
  have hRlt : R < 1 := by
    change (p : ℝ) ^ (-(k : ℤ)) < 1
    rw [zpow_neg, zpow_natCast, inv_lt_one₀ (pow_pos hpRpos k)]
    exact one_lt_pow₀ hpR (Nat.ne_of_gt hk)
  have hW : ‖W‖ ≤ R := by
    apply norm_sum_le hR
    intro j hj
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Padic.norm_int_le_one _)).trans
      (hVal j hj)
  have hFactor : W = (∑ j ∈ Finset.range n, (a j : ℚ_[p]) * coefficient m M S j) / A ^ q := by
    simp only [W, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  have hSign : (X - A ^ q) / A ^ q = -W := by
    calc
      (X - A ^ q) / A ^ q =
          -(∑ j ∈ Finset.range n, (a j : ℚ_[p]) * coefficient m M S j) / A ^ q := by
        apply congrArg (fun z : ℚ_[p] => z / A ^ q)
        rw [hExp]
        ring
      _ = -W := by rw [hFactor, neg_div]
  have hY : A ^ q ≠ 0 := pow_ne_zero _ hA
  have hnegW : ‖-W‖ ≤ R := by simpa only [norm_neg] using hW
  have hSmall : ‖-W‖ < 1 := hnegW.trans_lt hRlt
  have hX : X ≠ 0 := by
    intro hx
    have h := hSign
    rw [hx, zero_sub, neg_div, div_self hY] at h
    rw [← h, norm_neg, norm_one] at hSmall
    exact (lt_irrefl _ hSmall)
  have hU : ‖(X - A ^ q) / A ^ q‖ < 1 := by simpa only [hSign] using hSmall
  have hD : D = padicLog1p (-W) := by
    change padicLog p X - (q : ℚ_[p]) * padicLog p A = padicLog1p (-W)
    rw [← padicLog_pow p hA q, PadicExactBridge.spt1_padicLog1p_eq_binomial_log hSmall,
      ← hSign]
    exact paper1_log_difference_at_normalized_discrepancy p hX hY hU
  have hZero : padicLog1p (0 : ℚ_[p]) = 0 := by
    have hterm (j : ℕ) : Spt1.PadicLog.padicLogSeries (0 : ℚ_[p]) j = 0 := by
      cases j <;> simp [Spt1.PadicLog.padicLogSeries]
    simp [padicLog1p, hterm]
  have hDle : ‖D‖ ≤ R := by
    rw [hD]
    have h := PadicLipschitz.paper1_padic_log_one_lipschitz hSmall
      (by simp : ‖(0 : ℚ_[p])‖ < 1)
    simpa only [hZero, sub_zero] using h.trans (by simpa only [sub_zero] using hnegW)
  refine ⟨hSign, hD, hDle, ?_, ?_⟩
  · simpa only [sub_eq_add_neg, norm_neg] using
      (IsUltrametricDist.norm_add_le_max W (-D)).trans (max_le hW (by simpa using hDle))
  · intro hp3
    have h := PadicRemainder.paper1_odd_prime_log_quadratic_remainder hp3 k hk hnegW
    simpa only [← hD, sub_neg_eq_add] using h

/-- The displayed coefficient-sum congruence with the manuscript's
actual shifted binomial for all integer bases and modulus parameters. -/
theorem paper1_printed_shifted_binomial_log_congruence
    (n q m k : ℕ) (hk : 1 ≤ k) {A M : ℤ} {X : ℚ_[p]}
    (hA : A ≠ 0) (a : ℕ → ℤ)
    (hExp : (A : ℚ_[p]) ^ q = X + ∑ j ∈ Finset.range n,
      (a j : ℚ_[p]) * coefficient m (M : ℚ_[p]) (fun j => (shiftedBinomial A j : ℚ_[p])) j)
    (hVal : ∀ j < n, ‖coefficient m (M : ℚ_[p])
      (fun j => (shiftedBinomial A j : ℚ_[p])) j / (A : ℚ_[p]) ^ q‖ ≤ (p : ℝ) ^ (-(k : ℤ))) :
    ‖(∑ j ∈ Finset.range n, (a j : ℚ_[p]) *
      (coefficient m (M : ℚ_[p]) (fun j => (shiftedBinomial A j : ℚ_[p])) j /
        (A : ℚ_[p]) ^ q))
      - (padicLog p X - (q : ℚ_[p]) * padicLog p (A : ℚ_[p]))‖ ≤ (p : ℝ) ^ (-(k : ℤ)) :=
  (paper1_coefficient_transfer n q m k hk (Int.cast_ne_zero.mpr hA)
    a (fun j => (shiftedBinomial A j : ℚ_[p])) hExp hVal).2.2.2.1

end

end ManuscriptAudit.PadicCoefficientTransfer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicCoefficientTransfer.coefficient_div_eq_printed,
      ``ManuscriptAudit.PadicCoefficientTransfer.coefficient_mul_eq_printed,
      ``ManuscriptAudit.PadicCoefficientTransfer.shiftedBinomial_cast,
      ``ManuscriptAudit.PadicCoefficientTransfer.shiftedBinomial_padic_norm_le_one,
      ``ManuscriptAudit.PadicCoefficientTransfer.paper1_printed_coefficient_valuation,
      ``ManuscriptAudit.PadicCoefficientTransfer.paper1_power_modulus_norm_upper_bounds,
      ``ManuscriptAudit.PadicCoefficientTransfer.padic_norm_bound_of_valuation_threshold,
      ``ManuscriptAudit.PadicCoefficientTransfer.padic_norm_bound_iff_prime_power_integral_multiple,
      ``ManuscriptAudit.PadicCoefficientTransfer.paper1_coefficient_transfer,
      ``ManuscriptAudit.PadicCoefficientTransfer.paper1_printed_shifted_binomial_log_congruence] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
