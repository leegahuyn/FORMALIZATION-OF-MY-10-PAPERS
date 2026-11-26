import Lean.Util.CollectAxioms
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CuspPointCounts

/-!
# The actual point-count series of the cusp and its puncture

The coefficients are the actual point counts over each finite field
extension. Their difference is the contribution of the one rational
origin. The formal rational-series identities below use these counts
directly and require no trace-to-cohomology comparison.
-/

namespace ManuscriptAudit.CuspPointCountSeries

open PowerSeries CuspPointCounts

noncomputable section

private abbrev Series := ℚ⟦X⟧

/-- The geometric power series with successive coefficients qⁿ. -/
def geometric (q : ℚ) : Series := PowerSeries.mk fun n => q ^ n

theorem one_sub_mul_geometric (q : ℚ) :
    (1 - (X : Series) * C q) * geometric q = 1 := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul, mul_assoc]
  cases n with
  | zero =>
    simp only [map_sub, geometric, coeff_mk, pow_zero, coeff_zero_X_mul, sub_zero, coeff_zero_one]
  | succ n =>
    simp only [map_sub, coeff_succ_X_mul, coeff_C_mul, geometric, coeff_mk,
      coeff_one, Nat.succ_ne_zero, if_false]
    rw [pow_succ, mul_comm (q ^ n) q, sub_self]

/-- A series listing the point counts of the cusp in positive extension degrees. -/
def cuspSeries (p : ℕ) [Fact p.Prime] : Series :=
  X * PowerSeries.mk (fun n =>
    (Nat.card (curvePoints (GaloisField p (n + 1))) : ℚ))

/-- A series listing the point counts after removing the rational origin. -/
def punctureSeries (p : ℕ) [Fact p.Prime] : Series :=
  X * PowerSeries.mk (fun n =>
    (Nat.card (puncturedPoints (GaloisField p (n + 1))) : ℚ))

/-- The cusp count series is pT times the geometric series of ratio pT. -/
theorem cuspSeries_eq (p : ℕ) [Fact p.Prime] :
    cuspSeries p = X * (C (p : ℚ) * geometric (p : ℚ)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [cuspSeries, coeff_zero_X_mul]
  | succ n =>
    simp only [cuspSeries, coeff_succ_X_mul, coeff_C_mul, geometric, coeff_mk,
      (prime_power_point_counts p (n + 1) n.succ_ne_zero).1, Nat.cast_pow]
    rw [pow_succ, mul_comm]

/-- Removing the origin subtracts one coefficient in every positive degree. -/
theorem cuspSeries_sub_punctureSeries (p : ℕ) [Fact p.Prime] :
    cuspSeries p - punctureSeries p = X * geometric 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [map_sub, cuspSeries, punctureSeries, coeff_zero_X_mul, sub_zero]
  | succ n =>
    simp only [map_sub, cuspSeries, punctureSeries, coeff_succ_X_mul, geometric,
      coeff_mk, one_pow]
    have h :
        (Nat.card (puncturedPoints (GaloisField p (n + 1))) : ℚ) + 1 =
          (Nat.card (curvePoints (GaloisField p (n + 1))) : ℚ) := by
      exact_mod_cast punctured_add_one_card (GaloisField p (n + 1))
    linarith

/-- The signed difference has the formal rational identity T/(1−T). -/
theorem countDifference_rational_identity (p : ℕ) [Fact p.Prime] :
    (1 - (X : Series)) * (cuspSeries p - punctureSeries p) = X := by
  rw [cuspSeries_sub_punctureSeries]
  have h : (1 - (X : Series)) * geometric 1 = 1 := by
    simpa using one_sub_mul_geometric 1
  calc
    _ = X * ((1 - X) * geometric 1) := by ring
    _ = X := by rw [h, mul_one]

end

end ManuscriptAudit.CuspPointCountSeries

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspPointCountSeries.one_sub_mul_geometric,
      ``ManuscriptAudit.CuspPointCountSeries.cuspSeries_eq,
      ``ManuscriptAudit.CuspPointCountSeries.cuspSeries_sub_punctureSeries,
      ``ManuscriptAudit.CuspPointCountSeries.countDifference_rational_identity] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
