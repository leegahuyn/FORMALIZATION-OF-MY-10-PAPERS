import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricClassification
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedPointCounts

/-!
# Actual geometric p-torsion in the Paper 5 table

The first trace in each of the 28 printed rows is the trace of the
actual projective curve with parameter 1. The geometric criterion
below detects trivial p-torsion over the full algebraic closure.
-/

namespace ManuscriptAudit.Paper5PrintedSupersingular

open Paper5PrintedRecurrence (Row printedRows printedRows_prime)
open CubicGeometricTorsion (geometricPTorsionTrivial)

private theorem printedRows_prime_at_least_five :
    printedRows.all (fun r => decide (5 ≤ r.prime)) = true := by
  decide

/-- Triviality of the actual geometric p-torsion is equivalent to a zero
first trace for every row in the table. -/
theorem printedRows_geometric_p_torsion_trivial_iff {r : Row} (hr : r ∈ printedRows) :
    geometricPTorsionTrivial r.prime (printedRows_prime hr) (1 : ZMod r.prime) ↔ r.a1 = 0 := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  have hp5 : 5 ≤ r.prime :=
    of_decide_eq_true (List.all_eq_true.mp printedRows_prime_at_least_five r hr)
  have h := CubicGeometricClassification.paper5_trace_zero_iff_trivial_geometric_p_torsion
    hp5 (A := (1 : ZMod r.prime)) one_ne_zero
  rw [Paper5PrintedPointCounts.printedRows_actual_firstTrace hr] at h
  exact h.symm

/-- The zero-trace selector picks out precisely the actual geometrically
trivial p-torsion rows, with the membership proof needed for primality. -/
theorem mem_printedRows_zero_trace_iff {r : Row} :
    r ∈ printedRows.filter (fun row => decide (row.a1 = 0)) ↔
      ∃ hr : r ∈ printedRows,
        geometricPTorsionTrivial r.prime (printedRows_prime hr) (1 : ZMod r.prime) := by
  constructor
  · intro h
    obtain ⟨hr, hz⟩ := List.mem_filter.mp h
    exact ⟨hr, (printedRows_geometric_p_torsion_trivial_iff hr).mpr (of_decide_eq_true hz)⟩
  · rintro ⟨hr, ht⟩
    exact List.mem_filter.mpr
      ⟨hr, decide_eq_true ((printedRows_geometric_p_torsion_trivial_iff hr).mp ht)⟩

set_option maxRecDepth 4096 in
/-- The exact prime list of the rows picked out by the geometric criterion. -/
theorem printedRows_geometrically_trivial_p_torsion_primes :
    (printedRows.filter (fun r => decide (r.a1 = 0))).map Row.prime =
      [5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113] := by
  decide

/-- The first printed row has trivial geometric 5-torsion. -/
theorem printedRows_exists_trivial_geometric_p_torsion :
    ∃ (r : Row) (hr : r ∈ printedRows),
      r.prime = 5 ∧ geometricPTorsionTrivial r.prime (printedRows_prime hr) (1 : ZMod r.prime) := by
  let r : Row := ⟨3, 5, 6, 0, -10, 0, 50, 0, -250⟩
  have hr : r ∈ printedRows := by decide
  exact ⟨r, hr, rfl, (printedRows_geometric_p_torsion_trivial_iff hr).mpr rfl⟩

/-- A universal claim of nontrivial geometric p-torsion throughout the
printed table contradicts the points of the actual projective curves. -/
theorem not_all_printedRows_have_nontrivial_geometric_p_torsion :
    ¬ ∀ (r : Row) (hr : r ∈ printedRows),
      ¬ geometricPTorsionTrivial r.prime (printedRows_prime hr) (1 : ZMod r.prime) := by
  intro h
  obtain ⟨r, hr, _, ht⟩ := printedRows_exists_trivial_geometric_p_torsion
  exact h r hr ht

end ManuscriptAudit.Paper5PrintedSupersingular

open Lean Elab Command in
run_cmd do
  for name in [
      ``ManuscriptAudit.Paper5PrintedSupersingular.printedRows_geometric_p_torsion_trivial_iff,
      ``ManuscriptAudit.Paper5PrintedSupersingular.mem_printedRows_zero_trace_iff,
      ``ManuscriptAudit.Paper5PrintedSupersingular.printedRows_geometrically_trivial_p_torsion_primes,
      ``ManuscriptAudit.Paper5PrintedSupersingular.printedRows_exists_trivial_geometric_p_torsion,
      ``ManuscriptAudit.Paper5PrintedSupersingular.not_all_printedRows_have_nontrivial_geometric_p_torsion] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => x != `propext && x != `Classical.choice && x != `Quot.sound
    unless bad.isEmpty do
      throwError m!"{name} depends on forbidden axioms {bad}"
    logInfo m!"{name} uses {ax}"
