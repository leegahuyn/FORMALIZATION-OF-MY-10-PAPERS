import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterTables

/-!
# The rounded quadratic-root columns in Paper 5, page 166

The decimal columns are conjugate pairs. Both real parts are a/2.
For an imaginary magnitude printed as m/10^k, the half-unit rounding
interval for sqrt(4p-a²)/2 is checked after scaling and squaring.
-/

namespace ManuscriptAudit.Paper5LaterRootRounding

open Paper5LaterTables

structure RootDisplayRow where
  index : ℕ
  prime : ℕ
  twiceRealUpper : ℤ
  twiceRealLower : ℤ
  imagUpperNumerator : ℕ
  imagUpperDigits : ℕ
  imagLowerMagnitudeNumerator : ℕ
  imagLowerMagnitudeDigits : ℕ
  deriving DecidableEq

/-- The exact decimal numerators and displayed precision of both root columns. -/
def rootDisplayRows : List RootDisplayRow :=
  [⟨3, 5, 0, 0, 223607, 5, 223607, 5⟩,
   ⟨4, 7, 5, 5, 866025, 6, 866025, 6⟩,
   ⟨5, 11, 0, 0, 331662, 5, 331662, 5⟩,
   ⟨6, 13, -7, -7, 866025, 6, 866025, 6⟩,
   ⟨7, 17, 0, 0, 412311, 5, 412311, 5⟩,
   ⟨8, 19, -1, -1, 433013, 5, 433013, 5⟩,
   ⟨9, 23, 0, 0, 479583, 5, 479583, 5⟩,
   ⟨10, 29, 0, 0, 538516, 5, 538516, 5⟩,
   ⟨11, 31, -4, -4, 519615, 5, 519615, 5⟩,
   ⟨12, 37, -1, -1, 606218, 5, 606218, 5⟩,
   ⟨13, 41, 0, 0, 640312, 5, 640312, 5⟩,
   ⟨14, 43, 8, 8, 519615, 5, 519615, 5⟩,
   ⟨15, 47, 0, 0, 685565, 5, 685565, 5⟩,
   ⟨16, 53, 0, 0, 728011, 5, 728011, 5⟩,
   ⟨17, 59, 0, 0, 768115, 5, 768115, 5⟩,
   ⟨18, 61, -13, -13, 433013, 5, 433013, 5⟩,
   ⟨19, 67, 11, 11, 606218, 5, 606218, 5⟩,
   ⟨20, 71, 0, 0, 842615, 5, 842615, 5⟩,
   ⟨21, 73, 17, 17, 866025, 6, 866025, 6⟩,
   ⟨22, 79, -13, -13, 606218, 5, 606218, 5⟩,
   ⟨23, 83, 0, 0, 911043, 5, 911043, 5⟩,
   ⟨24, 89, 0, 0, 943398, 5, 943398, 5⟩,
   ⟨25, 97, 5, 5, 952628, 5, 952628, 5⟩,
   ⟨26, 101, 0, 0, 100499, 4, 100499, 4⟩,
   ⟨27, 103, -7, -7, 952628, 5, 952628, 5⟩,
   ⟨28, 107, 0, 0, 103441, 4, 103441, 4⟩,
   ⟨29, 109, 2, 2, 103923, 4, 103923, 4⟩,
   ⟨30, 113, 0, 0, 106301, 4, 106301, 4⟩]

def alignedRows : List (TateRow × RootDisplayRow) := tateRows.zip rootDisplayRows

/-- Integer inequalities for nearest-decimal rounding of the imaginary magnitude. -/
def roundedImaginary (p : ℕ) (a : ℤ) (m k : ℕ) : Prop :=
  0 < m ∧
  (2 * (m : ℤ) - 1) ^ 2 ≤ (4 * (p : ℤ) - a ^ 2) * 10 ^ (2 * k) ∧
  (4 * (p : ℤ) - a ^ 2) * 10 ^ (2 * k) ≤ (2 * (m : ℤ) + 1) ^ 2

private instance (p : ℕ) (a : ℤ) (m k : ℕ) : Decidable (roundedImaginary p a m k) := by
  unfold roundedImaginary
  infer_instance

theorem root_display_aligns :
    rootDisplayRows.map (fun r => (r.index, r.prime)) =
      tateRows.map (fun r => (r.index, r.prime)) := by decide

theorem displayed_real_and_conjugate_parts :
    ∀ r ∈ alignedRows,
      r.2.twiceRealUpper = r.1.trace ∧ r.2.twiceRealLower = r.1.trace ∧
      r.2.imagUpperNumerator = r.2.imagLowerMagnitudeNumerator ∧
      r.2.imagUpperDigits = r.2.imagLowerMagnitudeDigits := by decide

theorem both_imaginary_rounding_intervals :
    ∀ r ∈ alignedRows,
      roundedImaginary r.1.determinant r.1.trace r.2.imagUpperNumerator r.2.imagUpperDigits ∧
      roundedImaginary r.1.determinant r.1.trace r.2.imagLowerMagnitudeNumerator
        r.2.imagLowerMagnitudeDigits := by decide

end ManuscriptAudit.Paper5LaterRootRounding

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.Paper5LaterRootRounding.root_display_aligns,
        ``ManuscriptAudit.Paper5LaterRootRounding.displayed_real_and_conjugate_parts,
        ``ManuscriptAudit.Paper5LaterRootRounding.both_imaginary_rounding_intervals] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
