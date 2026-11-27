import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterAllTateCoefficients

/-! All powers of the actual Tate Frobenius in the later A = 4 table follow the printed recurrence. -/

namespace ManuscriptAudit.Paper5LaterAllTatePowers

open Paper5LaterTables PowerTateModule CubicFrobeniusSexticTwists
open CubicNonsplitTwoThreeAdicCharpoly Paper5PrintedSupersingular Paper5NonsplitFrobeniusModFour
open Paper5PrintedRecurrence

noncomputable section

private theorem row_metadata : ∀ r ∈ tateRows, r.prime.Prime ∧ 5 ≤ r.prime ∧
    r.determinant = r.prime := by decide

private theorem coefficient_prime {l : ℕ} (hl : l = 2 ∨ l = 3) : l.Prime := by
  rcases hl with rfl | rfl <;> decide

variable {r : TateRow} [Fact r.prime.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]

private def rowBasis (hr : r ∈ tateRows) (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    Basis (Fin 2) ℤ_[l] (Tate l (Geometric (ZMod r.prime) L 4)) := by
  obtain ⟨h₂, h₃⟩ := small_char r.prime (ZMod r.prime) (row_metadata r hr).2.1
  have h₄ : (4 : ZMod r.prime) ≠ 0 := by
    rw [show (4 : ZMod r.prime) = (2 : ZMod r.prime)^2 by ring]
    exact pow_ne_zero 2 h₂
  apply Classical.choice
  rcases hl with rfl | rfl
  · exact ⟨twoAdicBasis (ZMod r.prime) L h₂ h₃ h₄⟩
  · exact ⟨threeAdicBasis (ZMod r.prime) L h₂ h₃ h₄⟩

theorem trace_det_of_every_power (hr : r ∈ tateRows) (l : ℕ) (hl : l = 2 ∨ l = 3) (n : ℕ) :
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    let F := endMap l (arithmeticFrobenius (ZMod r.prime) L 4)
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod r.prime) L 4)) (F^n) =
      (recurrence r.prime r.trace n : ℤ_[l]) ∧
      LinearMap.det (F^n) = ((r.prime^n : ℕ) : ℤ_[l]) := by
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  let F := endMap l (arithmeticFrobenius (ZMod r.prime) L 4)
  obtain ⟨ht, hd⟩ := Paper5LaterAllTateCoefficients.trace_det hr L l hl
  rw [(row_metadata r hr).2.2] at hd
  change LinearMap.trace ℤ_[l] _ (F^n) = _ ∧ LinearMap.det (F^n) = _
  refine ⟨Paper5LinearTraceRecurrence.trace_pow_eq_recurrence
    (rowBasis L hr l hl) F r.prime r.trace ht hd n, ?_⟩
  rw [map_pow, hd, Nat.cast_pow]

end
end ManuscriptAudit.Paper5LaterAllTatePowers

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper5LaterAllTatePowers.trace_det_of_every_power
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
