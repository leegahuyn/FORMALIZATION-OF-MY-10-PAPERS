import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.Tactic.NormCast
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PadicBinomialLimit

/-!
# The p-adic logarithm on nonzero arguments

Paper 1, p. 7, uses a logarithmic difference when the ratio lies in
the principal units. Removing the valuation factor extends the unit
logarithm to all nonzero p-adic numbers with the choice \(\log(p)=0\).
-/

namespace ManuscriptAudit.PadicLogNonzero

open ManuscriptAudit.PadicBinomialLimit

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- Remove the power of the uniformizer from the argument. -/
def unitFactor (x : ℚ_[p]) : ℚ_[p] :=
  x / (p : ℚ_[p]) ^ x.valuation

private theorem prime_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- The unit factor has norm one for every nonzero p-adic number. -/
theorem norm_unitFactor {x : ℚ_[p]} (hx : x ≠ 0) : ‖unitFactor p x‖ = 1 := by
  rw [unitFactor, norm_div, Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_p_zpow]
  exact div_self (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

private theorem valuation_eq_zero_of_norm_one {x : ℚ_[p]} (hx : ‖x‖ = 1) :
    x.valuation = 0 := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by rw [hx]; exact zero_lt_one)
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpow : (p : ℝ) ^ (-x.valuation) = 1 :=
    (Padic.norm_eq_zpow_neg_valuation hx0).symm.trans hx
  exact neg_eq_zero.mp
    ((zpow_eq_one_iff_right₀ (zero_le_one.trans hp.le) hp.ne').mp hpow)

/-- A p-adic argument of norm one is already its own unit factor. -/
theorem unitFactor_eq_of_norm_one {x : ℚ_[p]} (hx : ‖x‖ = 1) :
    unitFactor p x = x := by
  rw [unitFactor, valuation_eq_zero_of_norm_one p hx, zpow_zero, div_one]

/-- Taking the unit factor commutes with division of nonzero arguments. -/
theorem unitFactor_div {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    unitFactor p (x / y) = unitFactor p x / unitFactor p y := by
  have hv : (x / y).valuation = x.valuation - y.valuation := by
    rw [div_eq_mul_inv, Padic.valuation_mul hx (inv_ne_zero hy),
      Padic.valuation_inv, sub_eq_add_neg]
  simp only [unitFactor, hv, zpow_sub₀ (prime_ne_zero p)]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private theorem unitFactor_pow (x : ℚ_[p]) (n : ℕ) :
    unitFactor p (x ^ n) = (unitFactor p x) ^ n := by
  have he : (p : ℚ_[p]) ^ ((n : ℤ) * x.valuation) =
      ((p : ℚ_[p]) ^ x.valuation) ^ n := by
    rw [mul_comm (n : ℤ), zpow_mul, zpow_natCast]
  simp only [unitFactor, Padic.valuation_pow, he, div_pow]

/-- The logarithm on nonzero p-adic numbers with \(\log(p)=0\). -/
def padicLog (x : ℚ_[p]) : ℚ_[p] :=
  padicLogUnit p (unitFactor p x)

/-- The extension agrees with the logarithm on norm-one units. -/
theorem padicLog_eq_unit_of_norm_one {x : ℚ_[p]} (hx : ‖x‖ = 1) :
    padicLog p x = padicLogUnit p x := by
  rw [padicLog, unitFactor_eq_of_norm_one p hx]

/-- The chosen p-adic logarithm vanishes on its uniformizer. -/
theorem padicLog_prime : padicLog p (p : ℚ_[p]) = 0 := by
  have hu : unitFactor p (p : ℚ_[p]) = 1 := by
    rw [unitFactor, Padic.valuation_p, zpow_one, div_self (prime_ne_zero p)]
  rw [padicLog, hu, padicLogUnit_eq_series_of_principal_unit p
    (by simp : ‖(1 : ℚ_[p]) - 1‖ < 1)]
  simp [padicLogSeries, zero_pow (Nat.succ_ne_zero _)]

theorem padicLog_one : padicLog p (1 : ℚ_[p]) = 0 := by
  rw [padicLog_eq_unit_of_norm_one p (norm_one : ‖(1 : ℚ_[p])‖ = 1),
    padicLogUnit_eq_series_of_principal_unit p
      (by simp : ‖(1 : ℚ_[p]) - 1‖ < 1)]
  simp [padicLogSeries, zero_pow (Nat.succ_ne_zero _)]

/-- On nonzero arguments the logarithm respects the quotient. -/
theorem padicLog_sub_eq_ratio {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicLog p x - padicLog p y = padicLog p (x / y) := by
  unfold padicLog
  rw [padicLogUnit_sub_eq_ratio p (norm_unitFactor p hx) (norm_unitFactor p hy),
    unitFactor_div p hx hy]

/-- The logarithm sends multiplication of nonzero p-adic numbers to addition. -/
theorem padicLog_mul {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicLog p (x * y) = padicLog p x + padicLog p y := by
  have h := padicLog_sub_eq_ratio p (mul_ne_zero hx hy) hy
  rw [mul_div_cancel_right₀ _ hy] at h
  exact sub_eq_iff_eq_add.mp h

theorem padicLog_inv {x : ℚ_[p]} (hx : x ≠ 0) :
    padicLog p x⁻¹ = -padicLog p x := by
  rw [← one_div, ← padicLog_sub_eq_ratio p one_ne_zero hx, padicLog_one, zero_sub]

/-- The difference of logarithms is the series at \(x/y-1\) when
the ratio is principal. Both arguments may have nonzero valuation. -/
theorem padicLog_sub_eq_series_of_principal_ratio {x y : ℚ_[p]}
    (hx : x ≠ 0) (hy : y ≠ 0) (hr : ‖x / y - 1‖ < 1) :
    padicLog p x - padicLog p y = padicLogSeries p (x / y - 1) := by
  rw [padicLog_sub_eq_ratio p hx hy,
    padicLog_eq_unit_of_norm_one p (norm_eq_one_of_principal_unit p hr),
    padicLogUnit_eq_series_of_principal_unit p hr]

/-- The Paper 1 logarithm difference with the displayed normalized discrepancy. -/
theorem paper1_log_difference_at_normalized_discrepancy {x y : ℚ_[p]}
    (hx : x ≠ 0) (hy : y ≠ 0) (hsmall : ‖(x - y) / y‖ < 1) :
    padicLog p x - padicLog p y = padicLogSeries p ((x - y) / y) := by
  have he : x / y - 1 = (x - y) / y := by rw [sub_div, div_self hy]
  rw [← he] at hsmall ⊢
  exact padicLog_sub_eq_series_of_principal_ratio p hx hy hsmall

/-- The logarithm of a natural power scales by that exponent. -/
theorem padicLog_pow {x : ℚ_[p]} (hx : x ≠ 0) (n : ℕ) :
    padicLog p (x ^ n) = (n : ℚ_[p]) * padicLog p x := by
  unfold padicLog
  rw [unitFactor_pow, padicLogUnit_pow p (norm_unitFactor p hx)]

end

end ManuscriptAudit.PadicLogNonzero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicLogNonzero.norm_unitFactor,
      ``ManuscriptAudit.PadicLogNonzero.unitFactor_eq_of_norm_one,
      ``ManuscriptAudit.PadicLogNonzero.unitFactor_div,
      ``ManuscriptAudit.PadicLogNonzero.padicLog_eq_unit_of_norm_one,
      ``ManuscriptAudit.PadicLogNonzero.padicLog_prime,
      ``ManuscriptAudit.PadicLogNonzero.padicLog_one,
      ``ManuscriptAudit.PadicLogNonzero.padicLog_sub_eq_ratio,
      ``ManuscriptAudit.PadicLogNonzero.padicLog_mul,
      ``ManuscriptAudit.PadicLogNonzero.padicLog_inv,
      ``ManuscriptAudit.PadicLogNonzero.padicLog_sub_eq_series_of_principal_ratio,
      ``ManuscriptAudit.PadicLogNonzero.paper1_log_difference_at_normalized_discrepancy,
      ``ManuscriptAudit.PadicLogNonzero.padicLog_pow] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
