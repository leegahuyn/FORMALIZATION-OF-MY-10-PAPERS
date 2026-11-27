import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedNonsplitTateTraces
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenPrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenPrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenPrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtyOnePrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtySevenPrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryFortyThreePrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySixtyOnePrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySixtySevenPrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySeventyThreePrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySeventyNinePrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNinetySevenPrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryOneHundredThreePrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryOneHundredNinePrintedTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenTwistTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTwistTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTwistTate

/-! All 168 printed values are native Frobenius power traces on both geometric Tate modules. -/

namespace ManuscriptAudit.Paper5PrintedAllTateTraces

open Paper5PrintedRecurrence Paper5PrintedPointCounts PowerTateModule
open Paper5PrintedNonsplitTateTraces

noncomputable section

private def splitRows : List Row :=
  [
   Paper5OrdinarySevenPrintedTrace.sevenRow,
   Paper5OrdinaryThirteenPrintedTrace.thirteenRow,
   Paper5OrdinaryNineteenPrintedTrace.nineteenRow,
   Paper5OrdinaryThirtyOnePrintedTrace.thirtyOneRow,
   Paper5OrdinaryThirtySevenPrintedTrace.thirtySevenRow,
   Paper5OrdinaryFortyThreePrintedTrace.fortyThreeRow,
   Paper5OrdinarySixtyOnePrintedTrace.sixtyOneRow,
   Paper5OrdinarySixtySevenPrintedTrace.sixtySevenRow,
   Paper5OrdinarySeventyThreePrintedTrace.seventyThreeRow,
   Paper5OrdinarySeventyNinePrintedTrace.seventyNineRow,
   Paper5OrdinaryNinetySevenPrintedTrace.ninetySevenRow,
   Paper5OrdinaryOneHundredThreePrintedTrace.oneHundredThreeRow,
   Paper5OrdinaryOneHundredNinePrintedTrace.oneHundredNineRow
  ]

theorem split_rows_exact :
    printedRows.filter (fun row => decide (row.prime % 3 ≠ 2)) = splitRows := by decide

private theorem seven_twist_trace_one :
    (Paper5OrdinarySevenTwistParameters.row (1 : ZMod 7)).trace =
      Paper5OrdinarySevenPrintedTrace.sevenRow.a1 := by decide

private theorem thirteen_twist_trace_one :
    (Paper5OrdinaryThirteenTwistParameters.row (1 : ZMod 13)).trace =
      Paper5OrdinaryThirteenPrintedTrace.thirteenRow.a1 := by decide

private theorem nineteen_twist_trace_one :
    (Paper5OrdinaryNineteenTwistParameters.row (1 : ZMod 19)).trace =
      Paper5OrdinaryNineteenPrintedTrace.nineteenRow.a1 := by decide

private theorem all_checked {r : Row} [primeRow : Fact r.prime.Prime] (hr : r ∈ printedRows)
    (L : Type*) [Field L] [algebraRow : Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    (List.range 6).map (fun i =>
      LinearMap.trace ℤ_[l] (Tate l (Points (r := r) L)) (actual (r := r) L l ^ (i + 1))) =
      r.traceColumns.map (fun a : ℤ => (a : ℤ_[l])) := by
  by_cases hn : r.prime % 3 = 2
  · exact six_nonsplit L l hr hn hl
  · have h : r ∈ splitRows := by
      rw [← split_rows_exact]
      exact List.mem_filter.mpr ⟨hr, by simp [hn]⟩
    letI charRow : CharP L r.prime :=
      charP_of_injective_algebraMap (algebraMap (ZMod r.prime) L).injective r.prime
    simp only [splitRows, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · letI : Algebra (ZMod 7) L := algebraRow
      letI : CharP L 7 := charRow
      letI : Fact (Nat.Prime 7) := primeRow
      have h1 : (1 : ZMod 7) ≠ 0 := one_ne_zero
      obtain ⟨ht, hd⟩ := Paper5OrdinarySevenTwistTate.trace_det L l hl
        (1 : ZMod 7) h1
      refine six_of_coefficients L l hr
        (Paper5OrdinarySevenTwistTate.tateBasis L l hl (1 : ZMod 7) h1) ?_ ?_
      · exact ht.trans (congrArg (fun a : ℤ => (a : ℤ_[l])) seven_twist_trace_one)
      · exact hd
    · letI : Algebra (ZMod 13) L := algebraRow
      letI : CharP L 13 := charRow
      letI : Fact (Nat.Prime 13) := primeRow
      have h1 : (1 : ZMod 13) ≠ 0 := one_ne_zero
      obtain ⟨ht, hd⟩ := Paper5OrdinaryThirteenTwistTate.trace_det L l hl
        (1 : ZMod 13) h1
      refine six_of_coefficients L l hr
        (Paper5OrdinaryThirteenTwistTate.tateBasis L l hl (1 : ZMod 13) h1) ?_ ?_
      · exact ht.trans (congrArg (fun a : ℤ => (a : ℤ_[l])) thirteen_twist_trace_one)
      · exact hd
    · letI : Algebra (ZMod 19) L := algebraRow
      letI : CharP L 19 := charRow
      letI : Fact (Nat.Prime 19) := primeRow
      have h1 : (1 : ZMod 19) ≠ 0 := one_ne_zero
      obtain ⟨ht, hd⟩ := Paper5OrdinaryNineteenTwistTate.trace_det L l hl
        (1 : ZMod 19) h1
      refine six_of_coefficients L l hr
        (Paper5OrdinaryNineteenTwistTate.tateBasis L l hl (1 : ZMod 19) h1) ?_ ?_
      · exact ht.trans (congrArg (fun a : ℤ => (a : ℤ_[l])) nineteen_twist_trace_one)
      · exact hd
    · letI : Algebra (ZMod 31) L := algebraRow
      letI : CharP L 31 := charRow
      exact Paper5OrdinaryThirtyOnePrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 37) L := algebraRow
      letI : CharP L 37 := charRow
      exact Paper5OrdinaryThirtySevenPrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 43) L := algebraRow
      letI : CharP L 43 := charRow
      exact Paper5OrdinaryFortyThreePrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 61) L := algebraRow
      letI : CharP L 61 := charRow
      exact Paper5OrdinarySixtyOnePrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 67) L := algebraRow
      letI : CharP L 67 := charRow
      exact Paper5OrdinarySixtySevenPrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 73) L := algebraRow
      letI : CharP L 73 := charRow
      exact Paper5OrdinarySeventyThreePrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 79) L := algebraRow
      letI : CharP L 79 := charRow
      exact Paper5OrdinarySeventyNinePrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 97) L := algebraRow
      letI : CharP L 97 := charRow
      exact Paper5OrdinaryNinetySevenPrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 103) L := algebraRow
      letI : CharP L 103 := charRow
      exact Paper5OrdinaryOneHundredThreePrintedTrace.six_trace_columns L l hl
    · letI : Algebra (ZMod 109) L := algebraRow
      letI : CharP L 109 := charRow
      exact Paper5OrdinaryOneHundredNinePrintedTrace.six_trace_columns L l hl

private theorem coefficient_prime {l : ℕ} (hl : l = 2 ∨ l = 3) : l.Prime := by
  rcases hl with rfl | rfl <;> decide

/-- For each of the 28 printed rows and either coefficient prime, all six printed columns are the
traces of the corresponding powers of the actual arithmetic Frobenius on the geometric Tate module
of the centered \(A=1\) cubic. -/
theorem all_printed_six_power_traces {r : Row} (hr : r ∈ printedRows)
    (L : Type*) [Field L] [algebraRow : Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) (hl : l = 2 ∨ l = 3) :
    letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    (List.range 6).map (fun i =>
      LinearMap.trace ℤ_[l] (Tate l (Points (r := r) L)) (actual (r := r) L l ^ (i + 1))) =
      r.traceColumns.map (fun a : ℤ => (a : ℤ_[l])) := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  exact all_checked hr L l hl

end
end ManuscriptAudit.Paper5PrintedAllTateTraces

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5PrintedAllTateTraces.split_rows_exact,
      ``ManuscriptAudit.Paper5PrintedAllTateTraces.all_printed_six_power_traces] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
