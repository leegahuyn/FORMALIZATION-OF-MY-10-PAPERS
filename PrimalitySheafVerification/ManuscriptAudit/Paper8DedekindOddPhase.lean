import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindPrimePhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindJacobiFloor

/-! The modulo-eight phase is exactly the Jacobi sign for every odd modulus. -/

namespace ManuscriptAudit.Paper8DedekindOddPhase

open Finset Paper8DedekindKloostermanCongruence Paper8DedekindFloorParity Paper8DedekindPrimePhase Paper8DedekindJacobiFloor

noncomputable section

theorem phase_mod_eight_jacobi {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1) (hC : h.Coprime k) :
    (dedekindPhaseNumerator h k : ZMod 8) =
      ((k : ZMod 8) - 1) * ((k : ZMod 8) - 2) - 2 +
        2 * ((jacobiSym (h : ℤ) k : ℤ) : ZMod 8) := by
  let Q := dedekindFloorWeight h k
  have hCast : (Q : ZMod 8) = ((Q % 2 : ℕ) : ZMod 8) + 2 * ((Q / 2 : ℕ) : ZMod 8) := by
    have hz := congrArg (fun n : ℕ => (n : ZMod 8)) (Nat.mod_add_div Q 2).symm
    push_cast at hz
    exact hz
  have hFour : 4 * (Q : ZMod 8) = (4 : ZMod 8) * ((Q % 2 : ℕ) : ZMod 8) := by
    conv_lhs =>
      rw [hCast, mul_add, ← mul_assoc, show (4 : ZMod 8) * 2 = 0 by decide, zero_mul, add_zero]
  have hSym : jacobiSym (h : ℤ) k = (-1 : ℤ) ^ (Q % 2) :=
    (jacobiSym_eq_weighted_floor h k hh hk hC).trans (neg_one_pow_eq_pow_mod_two _)
  have hSign : 4 * (Q : ZMod 8) = 2 - 2 * ((jacobiSym (h : ℤ) k : ℤ) : ZMod 8) := by
    rw [hFour, hSym]
    have hParity : Q % 2 = 0 ∨ Q % 2 = 1 := by omega
    rcases hParity with h | h <;> rw [h] <;> decide
  rw [phase_mod_eight_floor hh hk]
  change ((k : ZMod 8) - 1) * ((k : ZMod 8) - 2) - 4 * (Q : ZMod 8) = _
  rw [hSign]
  ring

end
end ManuscriptAudit.Paper8DedekindOddPhase

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindOddPhase.phase_mod_eight_jacobi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
