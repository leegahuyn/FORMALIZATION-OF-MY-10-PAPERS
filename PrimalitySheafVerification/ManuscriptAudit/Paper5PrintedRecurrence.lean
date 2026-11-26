import Lean.Util.CollectAxioms
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# The printed prime-power rows in Paper 5, page 158

The table is transcribed in printed order. The checks concern its integer
columns, the stated recurrence, and the squared Hasse inequalities.
-/

namespace ManuscriptAudit.Paper5PrintedRecurrence

structure Row where
  index : ℕ
  prime : ℕ
  points : ℕ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
  a5 : ℤ
  a6 : ℤ
  deriving DecidableEq

/-- Columns n, p, number of points, and the traces for powers p through p⁶. -/
def printedRows : List Row :=
  [⟨3, 5, 6, 0, -10, 0, 50, 0, -250⟩,
   ⟨4, 7, 12, -4, 2, 20, -94, 236, -286⟩,
   ⟨5, 11, 12, 0, -22, 0, 242, 0, -2662⟩,
   ⟨6, 13, 12, 2, -22, -70, 146, 1202, 506⟩,
   ⟨7, 17, 18, 0, -34, 0, 578, 0, -9826⟩,
   ⟨8, 19, 12, 8, 26, 56, -46, -1432, -10582⟩,
   ⟨9, 23, 24, 0, -46, 0, 1058, 0, -24334⟩,
   ⟨10, 29, 30, 0, -58, 0, 1682, 0, -48778⟩,
   ⟨11, 31, 36, -4, -46, 308, 194, -10324, 35282⟩,
   ⟨12, 37, 48, -10, 26, 110, -2062, 16550, -89206⟩,
   ⟨13, 41, 42, 0, -82, 0, 3362, 0, -137842⟩,
   ⟨14, 43, 36, 8, -22, -520, -3214, -3352, 111386⟩,
   ⟨15, 47, 48, 0, -94, 0, 4418, 0, -207646⟩,
   ⟨16, 53, 54, 0, -106, 0, 5618, 0, -297754⟩,
   ⟨17, 59, 60, 0, -118, 0, 6962, 0, -410758⟩,
   ⟨18, 61, 48, 14, 74, 182, -1966, -38626, -420838⟩,
   ⟨19, 67, 84, -16, 122, -880, 5906, -35536, 172874⟩,
   ⟨20, 71, 72, 0, -142, 0, 10082, 0, -715822⟩,
   ⟨21, 73, 84, -10, -46, 1190, -8542, -1450, 638066⟩,
   ⟨22, 79, 84, -4, -142, 884, 7682, -100564, -204622⟩,
   ⟨23, 83, 84, 0, -166, 0, 13778, 0, -1143574⟩,
   ⟨24, 89, 90, 0, -178, 0, 15842, 0, -1409938⟩,
   ⟨25, 97, 84, 14, 2, -1330, -18814, -134386, -56446⟩,
   ⟨26, 101, 102, 0, -202, 0, 20402, 0, -2060602⟩,
   ⟨27, 103, 84, 20, 194, 1820, 16418, 140900, 1126946⟩,
   ⟨28, 107, 108, 0, -214, 0, 22898, 0, -2450086⟩,
   ⟨29, 109, 108, 2, -214, -646, 22034, 114482, -2172742⟩,
   ⟨30, 113, 114, 0, -226, 0, 25538, 0, -2885794⟩]

def Row.traceColumns (r : Row) : List ℤ :=
  [r.a1, r.a2, r.a3, r.a4, r.a5, r.a6]

/-- The printed arithmetic recurrence, starting with a(p⁰) = 2 and a(p¹) = a. -/
def recurrence (p : ℕ) (a : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | n + 2 => a * recurrence p a (n + 1) - (p : ℤ) * recurrence p a n

def Row.recurrenceColumns (r : Row) : List ℤ :=
  (List.range 6).map (fun i => recurrence r.prime r.a1 (i + 1))

private def rowCheck (r : Row) : Prop :=
  r.prime.Prime ∧
  r.traceColumns = r.recurrenceColumns ∧
  (r.points : ℤ) = (r.prime : ℤ) + 1 - r.a1 ∧
  r.a1 ^ 2 ≤ 4 * (r.prime : ℤ) ∧
  ((List.range 6).all fun i =>
    decide (((r.traceColumns[i]?).getD 0) ^ 2 ≤ 4 * (r.prime : ℤ) ^ (i + 1))) = true

private instance (r : Row) : Decidable (rowCheck r) := by
  unfold rowCheck
  infer_instance

set_option maxRecDepth 4096 in
private theorem all_rowChecks :
    printedRows.all (fun r => decide (rowCheck r)) = true := by decide

private theorem rowCheck_of_mem {r : Row} (hr : r ∈ printedRows) : rowCheck r :=
  of_decide_eq_true (List.all_eq_true.mp all_rowChecks r hr)

theorem printedRows_length : printedRows.length = 28 := by decide

set_option maxRecDepth 4096 in
/-- The rows cover exactly indices 3 through 30 of the primes through 113. -/
theorem printedRows_prime_indices :
    printedRows.map (fun r => (r.index, r.prime)) =
      (((List.range 30).map (fun i => i + 1)).zip
        ((List.range 114).filter (fun p => decide p.Prime))).drop 2 := by decide

theorem printedRows_prime {r : Row} (hr : r ∈ printedRows) : r.prime.Prime :=
  (rowCheck_of_mem hr).1

/-- Each of the six trace columns agrees with the stated recurrence. -/
theorem printedRows_recurrence {r : Row} (hr : r ∈ printedRows) :
    r.traceColumns = r.recurrenceColumns :=
  (rowCheck_of_mem hr).2.1

/-- The printed point count column and the printed first trace agree arithmetically. -/
theorem printedRows_point_count_relation {r : Row} (hr : r ∈ printedRows) :
    (r.points : ℤ) = (r.prime : ℤ) + 1 - r.a1 :=
  (rowCheck_of_mem hr).2.2.1

/-- Every printed Hasse flag in the prime column agrees with its squared inequality. -/
theorem printedRows_hasse_squared {r : Row} (hr : r ∈ printedRows) :
    r.a1 ^ 2 ≤ 4 * (r.prime : ℤ) :=
  (rowCheck_of_mem hr).2.2.2.1

/-- The same squared bound also holds for each of the six displayed powers. -/
theorem printedRows_hasse_squared_at {r : Row} (hr : r ∈ printedRows) (i : Fin 6) :
    ((r.traceColumns[i.val]?).getD 0) ^ 2 ≤ 4 * (r.prime : ℤ) ^ (i.val + 1) :=
  of_decide_eq_true
    (List.all_eq_true.mp (rowCheck_of_mem hr).2.2.2.2 i.val (List.mem_range.mpr i.isLt))

set_option maxRecDepth 4096 in
/-- Exactly these rows contradict the printed claim that the first trace is
nonzero modulo the prime in every tested row. -/
theorem printedRows_trace_divisible_primes :
    (printedRows.filter (fun r => decide ((r.prime : ℤ) ∣ r.a1))).map Row.prime =
      [5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113] := by decide

end ManuscriptAudit.Paper5PrintedRecurrence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.Paper5PrintedRecurrence.printedRows_length,
        ``ManuscriptAudit.Paper5PrintedRecurrence.printedRows_prime_indices,
        ``ManuscriptAudit.Paper5PrintedRecurrence.printedRows_prime,
        ``ManuscriptAudit.Paper5PrintedRecurrence.printedRows_recurrence,
        ``ManuscriptAudit.Paper5PrintedRecurrence.printedRows_point_count_relation,
        ``ManuscriptAudit.Paper5PrintedRecurrence.printedRows_hasse_squared,
        ``ManuscriptAudit.Paper5PrintedRecurrence.printedRows_hasse_squared_at,
        ``ManuscriptAudit.Paper5PrintedRecurrence.printedRows_trace_divisible_primes] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
