import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic

/-! The exact finite twist parameters for centered cubics in characteristic seven. -/

namespace ManuscriptAudit.Paper5OrdinarySevenTwistParameters

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

structure Row where
  exponent : Fin 3
  negate : Bool
  trace : ℤ

/-- The sign and cube rotation relative to y²=x³+5, with its resulting degree-one trace. -/
def row (A : ZMod 7) : Row :=
  if A = 1 then ⟨1, true, -4⟩
  else if A = 2 then ⟨0, true, -1⟩
  else if A = 3 then ⟨2, false, -5⟩
  else if A = 4 then ⟨2, true, 5⟩
  else if A = 5 then ⟨0, false, 1⟩
  else if A = 6 then ⟨1, false, 4⟩
  else ⟨0, false, 0⟩

def ratio (A : ZMod 7) : ZMod 7 := 3 * A

def rotatedTrace (j : Fin 3) : ℤ :=
  if j = 0 then 1 else if j = 1 then 4 else -5

/-- The six nonzero coefficients give the displayed Frobenius conjugacy parameters. -/
theorem row_parameters : ∀ A : ZMod 7, A ≠ 0 →
    ratio A * 5 = A ∧ ratio A ^ 6 = 1 ∧
    ratio A ^ 2 = (2 : ZMod 7) ^ (row A).exponent.val ∧
    ratio A ^ 3 = (if (row A).negate then -1 else 1) ∧
    (row A).trace = (if (row A).negate then -rotatedTrace (row A).exponent
      else rotatedTrace (row A).exponent) := by
  decide

end ManuscriptAudit.Paper5OrdinarySevenTwistParameters

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinarySevenTwistParameters.row_parameters
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
