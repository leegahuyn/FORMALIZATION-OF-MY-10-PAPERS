import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.CompactModularCore

/-!
# The generators in Paper 8's multiplier calibration

The unit translation and inversion are not elements of the claimed group
on physical p. 337. The width-two translation does belong to the group.
-/

namespace ManuscriptAudit.Paper8MultiplierGroup

open LiteralCuspTruncation (GammaTwo)
open CompactModularCore (Reduced reduceTwo mem_gamma_iff_reduced_one)
open ModularGroup (T S)

theorem T_not_mem_GammaTwo : T ∉ GammaTwo := by
  intro h
  have hMatrix := (mem_gamma_iff_reduced_one T).mp h
  have hEntry := congrArg (fun a : Reduced => a 0 1) hMatrix
  exact (by decide : reduceTwo T 0 1 ≠ (1 : Reduced) 0 1) hEntry

theorem S_not_mem_GammaTwo : S ∉ GammaTwo := by
  intro h
  have hMatrix := (mem_gamma_iff_reduced_one S).mp h
  have hEntry := congrArg (fun a : Reduced => a 1 0) hMatrix
  exact (by decide : reduceTwo S 1 0 ≠ (1 : Reduced) 1 0) hEntry

theorem T_square_mem_GammaTwo : T ^ (2 : ℕ) ∈ GammaTwo := by
  apply (mem_gamma_iff_reduced_one _).mpr
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end ManuscriptAudit.Paper8MultiplierGroup

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MultiplierGroup.T_not_mem_GammaTwo,
      ``ManuscriptAudit.Paper8MultiplierGroup.S_not_mem_GammaTwo,
      ``ManuscriptAudit.Paper8MultiplierGroup.T_square_mem_GammaTwo] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
