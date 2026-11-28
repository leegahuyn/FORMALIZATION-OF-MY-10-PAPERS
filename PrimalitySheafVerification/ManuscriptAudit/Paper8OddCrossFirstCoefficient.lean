import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspCutoff

/-! The first signed cross modulus is exactly one. -/

namespace ManuscriptAudit.Paper8OddCrossFirstCoefficient

open Paper8OddCrossCuspCutoff Paper8OddCrossCuspRows
open Paper8DedekindZeroReference Paper8ContourResidueWeights

noncomputable section

theorem crossSum_one : crossSum (by decide : 0 < (1 : ℕ)) = 1 := by
  have hAll : (Finset.univ.filter (fun d : Fin 1 => Nat.Coprime d.val 1)) = Finset.univ := by
    ext d
    simp
  have hRef : referenceZeroSum 1 = 1 := by
    rw [referenceZeroSum, hAll, Fin.sum_univ_one]
    norm_num [dedekindSum, Fin.sum_univ_one, sawtooth]
  rw [crossSum_eq, hRef, mul_one] <;> norm_num [chiFour]

theorem crossRaw_zero : crossRaw 0 = 1 := by
  unfold crossRaw
  change crossSum (by decide : 0 < (1 : ℕ)) / (1 : ℂ) = 1
  rw [crossSum_one, div_one]

end
end ManuscriptAudit.Paper8OddCrossFirstCoefficient

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossFirstCoefficient.crossSum_one
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
