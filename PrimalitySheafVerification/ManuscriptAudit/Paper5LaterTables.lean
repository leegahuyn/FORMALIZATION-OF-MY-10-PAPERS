import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Sqrt
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedRecurrence

/-!
# The two computational tables in Paper 5, page 166

Page 165 introduces the panel as a user-supplied computation with a free
parameter A. The attached example script on page 167 sets A = 1.
The numeric panels below can be compared with page 158 independently
of which parameter was used to make the later tables.
-/

namespace ManuscriptAudit.Paper5LaterTables

structure CountRow where
  index : ℕ
  prime : ℕ
  points : ℕ
  trace : ℤ
  hasseFlag : Bool
  deriving DecidableEq

structure TateRow where
  index : ℕ
  prime : ℕ
  trace : ℤ
  determinant : ℕ
  ordinaryFlag : Bool
  deriving DecidableEq

/-- The exact integer columns and printed flags of the upper table. -/
def countRows : List CountRow :=
  [⟨3, 5, 6, 0, true⟩,
   ⟨4, 7, 3, 5, false⟩,
   ⟨5, 11, 12, 0, true⟩,
   ⟨6, 13, 21, -7, false⟩,
   ⟨7, 17, 18, 0, true⟩,
   ⟨8, 19, 21, -1, true⟩,
   ⟨9, 23, 24, 0, true⟩,
   ⟨10, 29, 30, 0, true⟩,
   ⟨11, 31, 36, -4, true⟩,
   ⟨12, 37, 39, -1, true⟩,
   ⟨13, 41, 42, 0, true⟩,
   ⟨14, 43, 36, 8, true⟩,
   ⟨15, 47, 48, 0, true⟩,
   ⟨16, 53, 54, 0, true⟩,
   ⟨17, 59, 60, 0, true⟩,
   ⟨18, 61, 75, -13, true⟩,
   ⟨19, 67, 57, 11, true⟩,
   ⟨20, 71, 72, 0, true⟩,
   ⟨21, 73, 57, 17, false⟩,
   ⟨22, 79, 93, -13, true⟩,
   ⟨23, 83, 84, 0, true⟩,
   ⟨24, 89, 90, 0, true⟩,
   ⟨25, 97, 93, 5, true⟩,
   ⟨26, 101, 102, 0, true⟩,
   ⟨27, 103, 111, -7, true⟩,
   ⟨28, 107, 108, 0, true⟩,
   ⟨29, 109, 108, 2, true⟩,
   ⟨30, 113, 114, 0, true⟩]

/-- The exact integer columns and printed ordinary flags of the lower table.
The conjugate eigenvalues in that table are displayed as rounded decimals. -/
def tateRows : List TateRow :=
  [⟨3, 5, 0, 5, false⟩,
   ⟨4, 7, 5, 7, true⟩,
   ⟨5, 11, 0, 11, false⟩,
   ⟨6, 13, -7, 13, true⟩,
   ⟨7, 17, 0, 17, false⟩,
   ⟨8, 19, -1, 19, true⟩,
   ⟨9, 23, 0, 23, false⟩,
   ⟨10, 29, 0, 29, false⟩,
   ⟨11, 31, -4, 31, true⟩,
   ⟨12, 37, -1, 37, true⟩,
   ⟨13, 41, 0, 41, false⟩,
   ⟨14, 43, 8, 43, true⟩,
   ⟨15, 47, 0, 47, false⟩,
   ⟨16, 53, 0, 53, false⟩,
   ⟨17, 59, 0, 59, false⟩,
   ⟨18, 61, -13, 61, true⟩,
   ⟨19, 67, 11, 67, true⟩,
   ⟨20, 71, 0, 71, false⟩,
   ⟨21, 73, 17, 73, true⟩,
   ⟨22, 79, -13, 79, true⟩,
   ⟨23, 83, 0, 83, false⟩,
   ⟨24, 89, 0, 89, false⟩,
   ⟨25, 97, 5, 97, true⟩,
   ⟨26, 101, 0, 101, false⟩,
   ⟨27, 103, -7, 103, true⟩,
   ⟨28, 107, 0, 107, false⟩,
   ⟨29, 109, 2, 109, true⟩,
   ⟨30, 113, 0, 113, false⟩]

/-- The same prime and index occur in the same row of each point-count table. -/
theorem tables_align :
    countRows.map (fun r => (r.index, r.prime)) =
      Paper5PrintedRecurrence.printedRows.map (fun r => (r.index, r.prime)) := by decide

/-- The point-column/trace relation in every row of the upper table. -/
theorem all_count_trace_relations :
    ∀ r ∈ countRows, (r.points : ℤ) = (r.prime : ℤ) + 1 - r.trace := by decide

/-- The exact trace, determinant, and ordinary labels of the lower table
are consistent with its paired upper-table data. -/
theorem tate_integer_columns :
    tateRows = countRows.map (fun r =>
      ⟨r.index, r.prime, r.trace, r.prime, decide (¬ (r.prime : ℤ) ∣ r.trace)⟩) := by decide

def pairedCounts : List (Paper5PrintedRecurrence.Row × CountRow) :=
  Paper5PrintedRecurrence.printedRows.zip countRows

theorem count_disagreement_primes :
    (pairedCounts.filter (fun r => decide (r.1.points ≠ r.2.points))).map (fun r => r.2.prime) =
      [7, 13, 19, 37, 61, 67, 73, 79, 97, 103] := by decide

theorem trace_disagreement_primes :
    (pairedCounts.filter (fun r => decide (r.1.a1 ≠ r.2.trace))).map (fun r => r.2.prime) =
      [7, 13, 19, 37, 61, 67, 73, 79, 97, 103] := by decide

theorem paired_primes_agree :
    ∀ r ∈ pairedCounts, r.1.prime = r.2.prime := by decide

/-- The floors in the page 169 script reproduce exactly the later table's flags. -/
theorem printed_flags_match_integer_sqrt :
    ∀ r ∈ countRows, r.hasseFlag = decide (r.trace.natAbs ≤ 2 * Nat.sqrt r.prime) := by decide

/-- The actual squared inequality holds in every row for the printed trace. -/
theorem all_printed_traces_satisfy_squared_hasse :
    ∀ r ∈ countRows, r.trace ^ 2 ≤ 4 * (r.prime : ℤ) := by decide

theorem false_hasse_no_primes :
    (countRows.filter (fun r => !r.hasseFlag)).map CountRow.prime = [7, 13, 73] := by decide

end ManuscriptAudit.Paper5LaterTables

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.Paper5LaterTables.tables_align,
        ``ManuscriptAudit.Paper5LaterTables.all_count_trace_relations,
        ``ManuscriptAudit.Paper5LaterTables.tate_integer_columns,
        ``ManuscriptAudit.Paper5LaterTables.count_disagreement_primes,
        ``ManuscriptAudit.Paper5LaterTables.trace_disagreement_primes,
        ``ManuscriptAudit.Paper5LaterTables.paired_primes_agree,
        ``ManuscriptAudit.Paper5LaterTables.printed_flags_match_integer_sqrt,
        ``ManuscriptAudit.Paper5LaterTables.all_printed_traces_satisfy_squared_hasse,
        ``ManuscriptAudit.Paper5LaterTables.false_hasse_no_primes] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
