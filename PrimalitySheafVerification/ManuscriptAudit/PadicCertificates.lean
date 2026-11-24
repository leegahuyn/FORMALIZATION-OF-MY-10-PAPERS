import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import PrimalitySheafVerification.Spt1

/-!
The p-adic logarithm series in Spt1 is summable on the norm ball.
This file derives the tail formula, convergence of its terms to zero,
and the nonarchimedean summability criterion. The certificate theorems
can be installed as local instances for existing results that use them.
-/

namespace ManuscriptAudit.PadicCertificates

open Filter Topology
open Spt1.PadicLog
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

/-- The logarithm minus its initial segment is the corresponding infinite tail. -/
theorem log_sub_trunc {x : ℚ_[p]} (hx : ‖x‖ < 1) (m : ℕ) :
    padicLog1p x - padicLogTrunc m x = ∑' i : ℕ, padicLogSeries x (i + m) := by
  have h := (padicLogSeries_summable hx).sum_add_tsum_nat_add m
  change padicLogTrunc m x + (∑' i : ℕ, padicLogSeries x (i + m)) = padicLog1p x at h
  exact (sub_eq_iff_eq_add).2 (h.symm.trans (add_comm _ _))

/-- The terms of the logarithm series tend to zero on its norm ball. -/
theorem series_tendsto_zero {x : ℚ_[p]} (hx : ‖x‖ < 1) :
    Tendsto (padicLogSeries x) atTop (nhds 0) :=
  (padicLogSeries_summable hx).tendsto_atTop_zero

/-- Convergence of the terms to zero implies summability in the complete
ultrametric p-adic field. -/
theorem series_summable_of_tendsto_zero {x : ℚ_[p]}
    (h : Tendsto (padicLogSeries x) atTop (nhds 0)) :
    Summable (padicLogSeries x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  simpa only [Nat.cofinite_eq_atTop] using h

theorem tailCertificate (p : ℕ) [Fact p.Prime] : PadicLogTailCertificate p := by
  constructor
  intro x hx m
  exact log_sub_trunc hx m

theorem tendstoCertificate (p : ℕ) [Fact p.Prime] : PadicLogTendstoCertificate p := by
  constructor
  intro x hx
  exact series_tendsto_zero hx

theorem nonarchSummabilityCertificate (p : ℕ) [Fact p.Prime] :
    PadicLogNonarchSummabilityCertificate p := by
  constructor
  intro x h
  exact series_summable_of_tendsto_zero h

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``log_sub_trunc, ``series_tendsto_zero, ``series_summable_of_tendsto_zero,
      ``tailCertificate, ``tendstoCertificate, ``nonarchSummabilityCertificate] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.PadicCertificates
