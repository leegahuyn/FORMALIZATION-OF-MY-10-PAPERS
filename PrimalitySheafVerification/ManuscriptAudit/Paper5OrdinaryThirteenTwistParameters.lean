import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic

/-! The six power-residue classes of centered cubics over the field of thirteen elements. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenTwistParameters

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

def ratio (A : ZMod 13) : ZMod 13 := A ^ 2

def rotatedTrace (j : Fin 3) : ℤ :=
  if j = 0 then 2 else if j = 1 then 5 else -7

structure Row where
  exponent : Fin 3
  negate : Bool
  trace : ℤ

/-- The cube rotation and ordinate sign depend only on the sextic power residue. -/
def row (A : ZMod 13) : Row :=
  let v := ratio A
  let j := if v ^ 2 = 1 then (0 : Fin 3) else if v ^ 2 = 3 then 1 else 2
  let neg := decide (v ^ 3 ≠ 1)
  ⟨j, neg, if neg then -rotatedTrace j else rotatedTrace j⟩

theorem row_parameters : ∀ A : ZMod 13, A ≠ 0 →
    ratio A ^ 6 = 1 ∧
    ratio A ^ 2 = (3 : ZMod 13) ^ (row A).exponent.val ∧
    ratio A ^ 3 = (if (row A).negate then -1 else 1) ∧
    (row A).trace = (if (row A).negate then -rotatedTrace (row A).exponent
      else rotatedTrace (row A).exponent) := by decide

end ManuscriptAudit.Paper5OrdinaryThirteenTwistParameters

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryThirteenTwistParameters.row_parameters
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
