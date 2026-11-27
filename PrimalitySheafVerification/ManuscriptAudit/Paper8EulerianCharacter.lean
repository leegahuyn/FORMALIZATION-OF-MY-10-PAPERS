import Lean.Util.CollectAxioms
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.LegendreSymbol
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorNormalization

/-! The exact positive-index Kronecker coefficient used in the Eulerian identity. -/

namespace ManuscriptAudit.Paper8EulerianCharacter

open Paper8ExteriorNormalization (kroneckerNegTwelve)

private theorem kronecker_nat_eq_jacobi_of_odd {m : ℕ} (hm : Odd m) :
    kroneckerNegTwelve (m : ℤ) = jacobiSym (-12) m := by
  have hMod : m % 2 = 1 := Nat.odd_iff.mp hm
  have hInt : (m : ℤ) % 2 ≠ 0 := by omega
  have hNonneg : ¬ (m : ℤ) < 0 := by omega
  simp [kroneckerNegTwelve, hInt, hNonneg]

theorem kronecker_nat_mod48 (m : ℕ) :
    kroneckerNegTwelve (m : ℤ) = kroneckerNegTwelve ((m % 48 : ℕ) : ℤ) := by
  by_cases hEven : m % 2 = 0
  · have hLeft : (m : ℤ) % 2 = 0 := by omega
    have hRight : ((m % 48 : ℕ) : ℤ) % 2 = 0 := by omega
    simp [kroneckerNegTwelve, hLeft, hRight]
  · have hOdd : Odd m := Nat.odd_iff.mpr (by omega)
    have hOddRem : Odd (m % 48) := Nat.odd_iff.mpr (by omega)
    rw [kronecker_nat_eq_jacobi_of_odd hOdd, kronecker_nat_eq_jacobi_of_odd hOddRem]
    simpa using jacobiSym.mod_right (-12) hOdd

set_option maxHeartbeats 1000000 in
theorem kronecker_nat_mod6 (m : ℕ) :
    kroneckerNegTwelve (m : ℤ) = if m % 6 = 1 then 1 else if m % 6 = 5 then -1 else 0 := by
  have h6 : (m % 48) % 6 = m % 6 := Nat.mod_mod_of_dvd _ (by decide : 6 ∣ 48)
  rw [kronecker_nat_mod48 m, ← h6]
  have hl : m % 48 < 48 := Nat.mod_lt _ (by decide)
  generalize hm : m % 48 = r at *
  interval_cases r <;> norm_num [kroneckerNegTwelve]

end ManuscriptAudit.Paper8EulerianCharacter

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EulerianCharacter.kronecker_nat_mod48,
      ``ManuscriptAudit.Paper8EulerianCharacter.kronecker_nat_mod6] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
