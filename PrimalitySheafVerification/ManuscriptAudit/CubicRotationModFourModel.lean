import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

/-! The exact fixed-point possibilities for the cubed order-three rotation algebra modulo four. -/

namespace ManuscriptAudit.CubicRotationModFourModel

abbrev Coordinates := ZMod 4 × ZMod 4

/-- The matrix of (a+bR) in the cyclic basis ((P, RP)) with (R^2+R+1=0). -/
def action (a b : ZMod 4) (v : Coordinates) : Coordinates :=
  (a * v.1 - b * v.2, b * v.1 + (a - b) * v.2)

def norm (a b : ZMod 4) : ZMod 4 := a ^ 2 - a * b + b ^ 2

def fixedCount (F : Coordinates → Coordinates) : ℕ :=
  (Finset.univ.filter (fun v => F v = v)).card

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- A cubic iterate and its negative both fix the points killed by two. For unit determinant
one, one of the two maps fixes all sixteen points. For determinant three, each fixes four. -/
theorem cube_fixed_patterns :
    ∀ a b : ZMod 4, norm a b = 1 ∨ norm a b = 3 →
      let F := fun v => action a b (action a b (action a b v))
      (∀ v : Coordinates, (2 : ℕ) • v = 0 → F v = v ∧ -F v = v) ∧
      ((norm a b = 1 ∧
        ((fixedCount F = 16 ∧ fixedCount (fun v => -F v) = 4) ∨
         (fixedCount F = 4 ∧ fixedCount (fun v => -F v) = 16))) ∨
       (norm a b = 3 ∧ fixedCount F = 4 ∧ fixedCount (fun v => -F v) = 4)) := by
  decide

end ManuscriptAudit.CubicRotationModFourModel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotationModFourModel.cube_fixed_patterns
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
