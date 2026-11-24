import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PadicBinomialLimit
import PrimalitySheafVerification.Spt1

/-!
# Exact logarithmic multiplication for the existing Paper 1 definition

The original series starts at degree zero with a zero summand. The
binomial-limit proof starts with degree one. Reindex the genuine
summable series and discharge the named additivity hypothesis in Spt1.
-/

namespace ManuscriptAudit.PadicExactBridge

open Spt1.PadicLog
theorem spt1_padicLog1p_eq_binomial_log {p : ℕ} [Fact p.Prime] {u : ℚ_[p]}
    (hu : ‖u‖ < 1) :
    padicLog1p u = PadicBinomialLimit.padicLogSeries p u := by
  have hterm (n : ℕ) :
      Spt1.PadicLog.padicLogSeries u (n + 1) =
        (-1 : ℚ_[p]) ^ n * u ^ (n + 1) / (n + 1 : ℚ_[p]) := by
    unfold Spt1.PadicLog.padicLogSeries
    rw [show n + 1 + 1 = n + 2 by rfl, pow_add (-1 : ℚ_[p]) n 2]
    simp only [neg_sq, one_pow, mul_one, Nat.cast_add, Nat.cast_one]
  symm
  simpa only [PadicBinomialLimit.padicLogSeries, padicLog1p, Finset.sum_range_one,
    padicLogSeries_zero_term, zero_add, hterm] using
    Summable.sum_add_tsum_nat_add 1 (padicLogSeries_summable hu)

theorem spt1_padicLog_additive (p : ℕ) [Fact p.Prime] : @PadicLogAdditive p _ := by
  intro u v hu hv
  rw [spt1_padicLog1p_eq_binomial_log (padicStar_norm_lt_one hu hv),
    spt1_padicLog1p_eq_binomial_log hu, spt1_padicLog1p_eq_binomial_log hv]
  exact PadicBinomialLimit.padicLogSeries_additive p hu hv

/-- Actual principal-unit logarithm power law for any natural exponent,
including the manuscript's indexed prime. -/
theorem paper1_principal_unit_log_power {p : ℕ} [Fact p.Prime] {u : ℚ_[p]}
    (hu : ‖u‖ < 1) (k : ℕ) :
    padicLog1p ((1 + u) ^ k - 1) = k • padicLog1p u := by
  have hs : starPow u k = (1 + u) ^ k - 1 := by
    rw [← one_add_starPow u k, add_comm (1 : ℚ_[p]), add_sub_cancel_right]
  have hbase : (1 + u : ℚ_[p]) - 1 = u := by ring
  have hbaseSmall : ‖(1 + u : ℚ_[p]) - 1‖ < 1 := by simpa only [hbase] using hu
  have hpowSmall : ‖(1 + u) ^ k - 1‖ < 1 := by
    rw [← hs]
    exact starPow_norm_lt_one hu k
  have hunit := PadicBinomialLimit.norm_eq_one_of_principal_unit p hbaseSmall
  have h := PadicBinomialLimit.padicLogUnit_pow p hunit k
  rw [PadicBinomialLimit.padicLogUnit_eq_series_of_principal_unit p hpowSmall,
    PadicBinomialLimit.padicLogUnit_eq_series_of_principal_unit p hbaseSmall, hbase] at h
  rw [spt1_padicLog1p_eq_binomial_log hpowSmall, spt1_padicLog1p_eq_binomial_log hu,
    nsmul_eq_mul]
  exact h

/-- The exact logarithm difference from Paper 1, p. 7, on units with
a principal-unit quotient. This uses the existing Spt1 series on the right. -/
theorem paper1_unit_log_difference_eq_spt1_log {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hq : ‖x / y - 1‖ < 1) :
    PadicBinomialLimit.padicLogUnit p x - PadicBinomialLimit.padicLogUnit p y =
      padicLog1p (x / y - 1) := by
  rw [PadicBinomialLimit.padicLogUnit_sub_eq_ratio p hx hy,
    PadicBinomialLimit.padicLogUnit_eq_series_of_principal_unit p hq,
    spt1_padicLog1p_eq_binomial_log hq]

end ManuscriptAudit.PadicExactBridge

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicExactBridge.spt1_padicLog1p_eq_binomial_log,
      ``ManuscriptAudit.PadicExactBridge.spt1_padicLog_additive,
      ``ManuscriptAudit.PadicExactBridge.paper1_principal_unit_log_power,
      ``ManuscriptAudit.PadicExactBridge.paper1_unit_log_difference_eq_spt1_log] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
