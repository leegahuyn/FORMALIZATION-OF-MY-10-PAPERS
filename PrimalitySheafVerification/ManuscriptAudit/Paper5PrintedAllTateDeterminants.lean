import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedAllTateTraces

/-! The first two audited trace columns determine the native Tate determinant in every row. -/

namespace ManuscriptAudit.Paper5PrintedAllTateDeterminants

open Paper5PrintedRecurrence Paper5PrintedNonsplitTateTraces Paper5PrintedAllTateTraces
open CubicNonsplitTwoThreeAdicCharpoly Paper5NonsplitFrobeniusModFour Paper5PrintedSupersingular
open PowerTateModule Module

noncomputable section

private theorem trace_square {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (B : Basis (Fin 2) R M) (F : Module.End R M) :
    LinearMap.trace R M (F ^ 2) =
      (LinearMap.trace R M F) ^ 2 - 2 * LinearMap.det F := by
  rw [LinearMap.trace_eq_matrix_trace R B (F ^ 2), LinearMap.trace_eq_matrix_trace R B F,
    ← LinearMap.det_toMatrix B, pow_two, LinearMap.toMatrix_mul]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

private theorem coefficient_prime {l : ℕ} (hl : l = 2 ∨ l = 3) : l.Prime := by
  rcases hl with rfl | rfl <;> decide

private def rowBasis {r : Row} [Fact r.prime.Prime] (hr : r ∈ printedRows)
    (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    Basis (Fin 2) ℤ_[l] (Tate l (Points (r := r) L)) := by
  obtain ⟨h₂, h₃⟩ := small_char r.prime (ZMod r.prime) (printedRows_prime_at_least_five hr)
  apply Classical.choice
  rcases hl with rfl | rfl
  · exact ⟨twoAdicBasis (ZMod r.prime) L h₂ h₃ (one_ne_zero : (1 : ZMod r.prime) ≠ 0)⟩
  · exact ⟨threeAdicBasis (ZMod r.prime) L h₂ h₃ (one_ne_zero : (1 : ZMod r.prime) ≠ 0)⟩

private theorem checked_coefficients {r : Row} [Fact r.prime.Prime] (hr : r ∈ printedRows)
    (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points (r := r) L)) (actual (r := r) L l) = (r.a1 : ℤ_[l]) ∧
      LinearMap.det (actual (r := r) L l) = (r.prime : ℤ_[l]) := by
  let V := Tate l (Points (r := r) L)
  let F := actual (r := r) L l
  have h := all_printed_six_power_traces hr L l hl
  have ht : LinearMap.trace ℤ_[l] V F = (r.a1 : ℤ_[l]) := by
    have e := congrArg (fun s : List ℤ_[l] => (s[0]?).getD 0) h
    change LinearMap.trace ℤ_[l] V (F ^ 1) = (r.a1 : ℤ_[l]) at e
    simpa only [pow_one] using e
  have hs : LinearMap.trace ℤ_[l] V (F ^ 2) =
      (r.a1 : ℤ_[l]) * (r.a1 : ℤ_[l]) - (r.prime : ℤ_[l]) * 2 := by
    have e := congrArg (fun s : List ℤ_[l] => (s[1]?).getD 0) h
    change LinearMap.trace ℤ_[l] V (F ^ 2) = (r.a2 : ℤ_[l]) at e
    have hrow := congrArg (fun s : List ℤ => (s[1]?).getD 0) (printedRows_recurrence hr)
    change r.a2 = r.a1 * r.a1 - (r.prime : ℤ) * 2 at hrow
    simpa only [hrow, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] using e
  have hid := trace_square (rowBasis hr L l hl) F
  rw [ht, hs] at hid
  have hc : (2 : ℤ_[l]) * LinearMap.det F = 2 * (r.prime : ℤ_[l]) := by
    linear_combination hid
  exact ⟨ht, mul_left_cancel₀ (by exact two_ne_zero) hc⟩

/-- Every Frobenius power in each printed row has its native determinant at both coefficient primes. -/
theorem all_printed_power_determinants {r : Row} (hr : r ∈ printedRows)
    (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) (hl : l = 2 ∨ l = 3) (n : ℕ) :
    letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    LinearMap.det (actual (r := r) L l ^ n) = ((r.prime ^ n : ℕ) : ℤ_[l]) := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  rw [map_pow, (checked_coefficients hr L l hl).2, Nat.cast_pow]

/-- The printed recurrence gives the native traces beyond the six displayed powers. -/
theorem all_printed_power_traces {r : Row} (hr : r ∈ printedRows)
    (L : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
    (l : ℕ) (hl : l = 2 ∨ l = 3) (n : ℕ) :
    letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
    letI : Fact l.Prime := ⟨coefficient_prime hl⟩
    LinearMap.trace ℤ_[l] (Tate l (Points (r := r) L)) (actual (r := r) L l ^ n) =
      (recurrence r.prime r.a1 n : ℤ_[l]) := by
  letI : Fact r.prime.Prime := ⟨printedRows_prime hr⟩
  letI : Fact l.Prime := ⟨coefficient_prime hl⟩
  obtain ⟨ht, hd⟩ := checked_coefficients hr L l hl
  exact Paper5LinearTraceRecurrence.trace_pow_eq_recurrence
    (rowBasis hr L l hl) (actual (r := r) L l) r.prime r.a1 ht hd n

end
end ManuscriptAudit.Paper5PrintedAllTateDeterminants

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5PrintedAllTateDeterminants.all_printed_power_determinants,
      ``ManuscriptAudit.Paper5PrintedAllTateDeterminants.all_printed_power_traces] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
