import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterTables

/-! Exact rounding intervals for all imaginary coordinates printed on physical p. 166. -/

namespace ManuscriptAudit.Paper5LaterRoundedEigenvalues

open Paper5LaterTables

/-- The displayed positive imaginary part in each row, as an integer and a decimal scale. -/
def imaginaryDigits : List (ℤ × ℤ) :=
  [(223607, 100000),
   (866025, 1000000),
   (331662, 100000),
   (866025, 1000000),
   (412311, 100000),
   (433013, 100000),
   (479583, 100000),
   (538516, 100000),
   (519615, 100000),
   (606218, 100000),
   (640312, 100000),
   (519615, 100000),
   (685565, 100000),
   (728011, 100000),
   (768115, 100000),
   (433013, 100000),
   (606218, 100000),
   (842615, 100000),
   (866025, 1000000),
   (606218, 100000),
   (911043, 100000),
   (943398, 100000),
   (952628, 100000),
   (100499, 10000),
   (952628, 100000),
   (103441, 10000),
   (103923, 10000),
   (106301, 10000)]

def annotated : List (TateRow × (ℤ × ℤ)) :=
  tateRows.zip imaginaryDigits

def radicand (r : TateRow) : ℤ :=
  4 * (r.determinant : ℤ) - r.trace ^ 2

theorem all_rows_annotated : annotated.map Prod.fst = tateRows := by decide

/-- Every exact scaled radicand lies strictly between the two squared half-unit endpoints. -/
theorem integer_brackets : ∀ r ∈ annotated,
    0 < r.2.1 ∧ 0 < r.2.2 ∧ 0 < radicand r.1 ∧
      (2 * r.2.1 - 1)^2 < radicand r.1 * r.2.2^2 ∧
      radicand r.1 * r.2.2^2 < (2 * r.2.1 + 1)^2 := by decide

/-- The positive imaginary part of the quadratic roots rounds to the printed digits. -/
theorem imaginary_part_rounds {r : TateRow × (ℤ × ℤ)} (hr : r ∈ annotated) :
    ((r.2.1 : ℝ) - 1 / 2) / (r.2.2 : ℝ) < Real.sqrt (radicand r.1) / 2 ∧
      Real.sqrt (radicand r.1) / 2 < ((r.2.1 : ℝ) + 1 / 2) / (r.2.2 : ℝ) := by
  obtain ⟨ha, hs, hD, hlo, hhi⟩ := integer_brackets r hr
  let a : ℝ := r.2.1
  let s : ℝ := r.2.2
  let D : ℝ := radicand r.1
  have hs' : 0 < s := by exact_mod_cast hs
  have hD' : 0 < D := by exact_mod_cast hD
  have ha' : 1 ≤ a := by exact_mod_cast (show 1 ≤ r.2.1 by omega)
  have hlo' : (2 * a - 1)^2 < D * s^2 := by
    dsimp only [a, s, D]
    exact_mod_cast hlo
  have hhi' : D * s^2 < (2 * a + 1)^2 := by
    dsimp only [a, s, D]
    exact_mod_cast hhi
  have hsq : (s * Real.sqrt D)^2 = D * s^2 := by
    rw [mul_pow, Real.sq_sqrt hD'.le, mul_comm]
  have hn : 0 ≤ s * Real.sqrt D := mul_nonneg hs'.le (Real.sqrt_nonneg _)
  have hlSq : (2 * a - 1)^2 < (s * Real.sqrt D)^2 := by simpa only [hsq] using hlo'
  have hhSq : (s * Real.sqrt D)^2 < (2 * a + 1)^2 := by simpa only [hsq] using hhi'
  have hlow := (sq_lt_sq₀ (show 0 ≤ 2 * a - 1 by linarith) hn).mp hlSq
  have hhigh := (sq_lt_sq₀ hn (show 0 ≤ 2 * a + 1 by linarith)).mp hhSq
  change (a - 1 / 2) / s < Real.sqrt D / 2 ∧ Real.sqrt D / 2 < (a + 1 / 2) / s
  constructor
  · apply (div_lt_iff₀ hs').mpr
    nlinarith only [hlow]
  · apply (lt_div_iff₀ hs').mpr
    nlinarith only [hhigh]

end ManuscriptAudit.Paper5LaterRoundedEigenvalues

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterRoundedEigenvalues.all_rows_annotated,
      ``ManuscriptAudit.Paper5LaterRoundedEigenvalues.integer_brackets,
      ``ManuscriptAudit.Paper5LaterRoundedEigenvalues.imaginary_part_rounds] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
