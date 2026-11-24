import Lean.Util.CollectAxioms
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
    rw [R, zpow_neg, zpow_natCast, inv_lt_one₀ (pow_pos hpRpos k)]
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
    rw [D, ← padicLog_pow p hA q, PadicExactBridge.spt1_padicLog1p_eq_binomial_log hSmall,
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

end

end ManuscriptAudit.PadicCoefficientTransfer

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PadicCoefficientTransfer.paper1_coefficient_transfer
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
