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
      · have hT : (Paper5OrdinarySevenTwistParameters.row (1 : ZMod 7)).trace =
            Paper5OrdinarySevenPrintedTrace.sevenRow.a1 := by decide
        exact ht.trans (congrArg (fun a : ℤ => (a : ℤ_[l])) hT)
      · letI : Algebra (ZMod 7) L := algebraRow
      letI : CharP L 7 := charRow
      letI : Fact (Nat.Prime 7) := primeRow
      have h1 : (1 : ZMod 7) ≠ 0 := one_ne_zero
      simpa only [Paper5OrdinarySevenPrintedTrace.sevenRow, Nat.cast_ofNat] using hd
    · letI : Algebra (ZMod 13) L := algebraRow
      letI : CharP L 13 := charRow
      letI : Fact (Nat.Prime 13) := primeRow
      have h1 : (1 : ZMod 13) ≠ 0 := one_ne_zero
      obtain ⟨ht, hd⟩ := Paper5OrdinaryThirteenTwistTate.trace_det L l hl
        (1 : ZMod 13) h1
      refine six_of_coefficients L l hr
        (Paper5OrdinaryThirteenTwistTate.tateBasis L l hl (1 : ZMod 13) h1) ?_ ?_
      · have hT : (Paper5OrdinaryThirteenTwistParameters.row (1 : ZMod 13)).trace =
            Paper5OrdinaryThirteenPrintedTrace.thirteenRow.a1 := by decide
        exact ht.trans (congrArg (fun a : ℤ => (a : ℤ_[l])) hT)
      · letI : Algebra (ZMod 13) L := algebraRow
      letI : CharP L 13 := charRow
      letI : Fact (Nat.Prime 13) := primeRow
      have h1 : (1 : ZMod 13) ≠ 0 := one_ne_zero
      simpa only [Paper5OrdinaryThirteenPrintedTrace.thirteenRow, Nat.cast_ofNat] using hd
    · letI : Algebra (ZMod 19) L := algebraRow
      letI : CharP L 19 := charRow
      letI : Fact (Nat.Prime 19) := primeRow
      have h1 : (1 : ZMod 19) ≠ 0 := one_ne_zero
      obtain ⟨ht, hd⟩ := Paper5OrdinaryNineteenTwistTate.trace_det L l hl
        (1 : ZMod 19) h1
      refine six_of_coefficients L l hr
        (Paper5OrdinaryNineteenTwistTate.tateBasis L l hl (1 : ZMod 19) h1) ?_ ?_
      · have hT : (Paper5OrdinaryNineteenTwistParameters.row (1 : ZMod 19)).trace =
            Paper5OrdinaryNineteenPrintedTrace.nineteenRow.a1 := by decide
        exact ht.trans (congrArg (fun a : ℤ => (a : ℤ_[l])) hT)
      · letI : Algebra (ZMod 19) L := algebraRow
      letI : CharP L 19 := charRow
      letI : Fact (Nat.Prime 19) := primeRow
      have h1 : (1 : ZMod 19) ≠ 0 := one_ne_zero
      simpa only [Paper5OrdinaryNineteenPrintedTrace.nineteenRow, Nat.cast_ofNat] using hd
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

private theorem determinant_checked {r : Row} [primeRow : Fact r.prime.Prime] (hr : r ∈ printedRows)
    (L : Type*) [Field L] [algebraRow : Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.det (actual (r := r) L l) = (r.prime : ℤ_[l]) := by
  by_cases hn : r.prime % 3 = 2
  · obtain ⟨h₂, h₃⟩ := Paper5NonsplitFrobeniusModFour.small_char r.prime (ZMod r.prime)
      (Paper5PrintedSupersingular.printedRows_prime_at_least_five hr)
    have hq : Fintype.card (ZMod r.prime) % 3 = 2 := by simpa only [ZMod.card] using hn
    rcases hl with rfl | rfl
    · simpa only [ZMod.card] using
        CubicNonsplitTwoThreeAdicCharpoly.two_adic_determinant (ZMod r.prime) L h₂ h₃ one_ne_zero hq
    · simpa only [ZMod.card] using
        CubicNonsplitTwoThreeAdicCharpoly.three_adic_determinant (ZMod r.prime) L h₂ h₃ one_ne_zero hq
  · have h : r ∈ splitRows := by
      rw [← split_rows_exact]
      exact List.mem_filter.mpr ⟨hr, by simp [hn]⟩
    letI charRow : CharP L r.prime :=
      charP_of_injective_algebraMap (algebraMap (ZMod r.prime) L).injective r.prime
    simp only [splitRows, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [Paper5OrdinarySevenPrintedTrace.sevenRow, Nat.cast_ofNat] using
        (Paper5OrdinarySevenTwistTate.trace_det L l hl (1 : ZMod 7) h1).2
    · simpa only [Paper5OrdinaryThirteenPrintedTrace.thirteenRow, Nat.cast_ofNat] using
        (Paper5OrdinaryThirteenTwistTate.trace_det L l hl (1 : ZMod 13) h1).2
    · simpa only [Paper5OrdinaryNineteenPrintedTrace.nineteenRow, Nat.cast_ofNat] using
        (Paper5OrdinaryNineteenTwistTate.trace_det L l hl (1 : ZMod 19) h1).2
    · letI : Algebra (ZMod 31) L := algebraRow
      letI : CharP L 31 := charRow
      simpa only [Paper5OrdinaryThirtyOnePrintedTrace.thirtyOneRow, Nat.cast_ofNat] using
        (Paper5OrdinaryThirtyOneTate.trace_det L l hl).2
    · letI : Algebra (ZMod 37) L := algebraRow
      letI : CharP L 37 := charRow
      simpa only [Paper5OrdinaryThirtySevenPrintedTrace.thirtySevenRow, Nat.cast_ofNat] using
        (Paper5OrdinaryThirtySevenTate.trace_det L l hl).2
    · letI : Algebra (ZMod 43) L := algebraRow
      letI : CharP L 43 := charRow
      simpa only [Paper5OrdinaryFortyThreePrintedTrace.fortyThreeRow, Nat.cast_ofNat] using
        (Paper5OrdinaryFortyThreeTate.trace_det L l hl).2
    · letI : Algebra (ZMod 61) L := algebraRow
      letI : CharP L 61 := charRow
      simpa only [Paper5OrdinarySixtyOnePrintedTrace.sixtyOneRow, Nat.cast_ofNat] using
        (Paper5OrdinarySixtyOneTate.trace_det L l hl).2
    · letI : Algebra (ZMod 67) L := algebraRow
      letI : CharP L 67 := charRow
      simpa only [Paper5OrdinarySixtySevenPrintedTrace.sixtySevenRow, Nat.cast_ofNat] using
        (Paper5OrdinarySixtySevenTate.trace_det L l hl).2
    · letI : Algebra (ZMod 73) L := algebraRow
      letI : CharP L 73 := charRow
      simpa only [Paper5OrdinarySeventyThreePrintedTrace.seventyThreeRow, Nat.cast_ofNat] using
        (Paper5OrdinarySeventyThreeTate.trace_det L l hl).2
    · letI : Algebra (ZMod 79) L := algebraRow
      letI : CharP L 79 := charRow
      simpa only [Paper5OrdinarySeventyNinePrintedTrace.seventyNineRow, Nat.cast_ofNat] using
        (Paper5OrdinarySeventyNineTate.trace_det L l hl).2
    · letI : Algebra (ZMod 97) L := algebraRow
      letI : CharP L 97 := charRow
      simpa only [Paper5OrdinaryNinetySevenPrintedTrace.ninetySevenRow, Nat.cast_ofNat] using
        (Paper5OrdinaryNinetySevenTate.trace_det L l hl).2
    · letI : Algebra (ZMod 103) L := algebraRow
      letI : CharP L 103 := charRow
      simpa only [Paper5OrdinaryOneHundredThreePrintedTrace.oneHundredThreeRow, Nat.cast_ofNat] using
        (Paper5OrdinaryOneHundredThreeTate.trace_det L l hl).2
    · letI : Algebra (ZMod 109) L := algebraRow
      letI : CharP L 109 := charRow
      simpa only [Paper5OrdinaryOneHundredNinePrintedTrace.oneHundredNineRow, Nat.cast_ofNat] using
        (Paper5OrdinaryOneHundredNineTate.trace_det L l hl).2

/-- In each printed row, every power of the arithmetic Frobenius has its exact determinant on
either geometric Tate module. -/
theorem all_printed_power_determinants {r : Row} (hr : r ∈ printedRows)
    (L : Type*) [Field L] [algebraRow : Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) (hl : l = 2 ∨ l = 3) (n : ℕ) :
    letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    LinearMap.det (actual (r := r) L l ^ n) = ((r.prime ^ n : ℕ) : ℤ_[l]) := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  rw [map_pow, determinant_checked hr L l hl, Nat.cast_pow]

end
end ManuscriptAudit.Paper5PrintedAllTateTraces

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5PrintedAllTateTraces.split_rows_exact,
      ``ManuscriptAudit.Paper5PrintedAllTateTraces.all_printed_six_power_traces,
      ``ManuscriptAudit.Paper5PrintedAllTateTraces.all_printed_power_determinants] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
