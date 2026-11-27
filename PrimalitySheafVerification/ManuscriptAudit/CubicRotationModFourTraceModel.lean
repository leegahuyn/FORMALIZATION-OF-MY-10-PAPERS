import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationModFourModel

/-! Additional trace alternatives when the mod-four rotation norm is one. -/

namespace ManuscriptAudit.CubicRotationModFourTraceModel

open CubicRotationModFourModel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Norm-one operators of even trace fix all the points killed by two. The two odd trace
alternatives fix only zero at level two and have distinct cube fixed counts at level four. -/
theorem trace_fixed_patterns :
    ∀ a b : ZMod 4, norm a b = 1 →
      let F := action a b
      let F₃ := fun v => F (F (F v))
      let t := 2 * a - b
      (t = 2 ∧ ∀ v : Coordinates, (2 : ℕ) • v = 0 → F v = v) ∨
      (t = 1 ∧ (∀ v : Coordinates, (2 : ℕ) • v = 0 → F v = v → v = 0) ∧
        fixedCount F₃ = 4) ∨
      (t = 3 ∧ (∀ v : Coordinates, (2 : ℕ) • v = 0 → F v = v → v = 0) ∧
        fixedCount F₃ = 16) := by
  decide

end ManuscriptAudit.CubicRotationModFourTraceModel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotationModFourTraceModel.trace_fixed_patterns
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
