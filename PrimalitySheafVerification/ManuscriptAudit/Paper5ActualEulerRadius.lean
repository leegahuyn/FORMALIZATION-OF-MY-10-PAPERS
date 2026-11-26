import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicHasseBound
import PrimalitySheafVerification.ManuscriptAudit.EllipticQuadraticRadius

/-! The literal local factor for the actual good cubic reduction has the stated root circle. -/

namespace ManuscriptAudit.Paper5ActualEulerRadius

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open EllipticQuadraticRadius

noncomputable section

/-- Using the actual projective point count, all reciprocal roots have radius p⁻¹ᐟ². -/
theorem actual_reduced_cubic_roots_on_circle (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) (z : ℂ)
    (hz : (localPolynomial (p : ℝ) ((p : ℝ) + 1 -
      (Nat.card (paper5TraceCurve p A).toProjective.Point : ℝ))).IsRoot z) :
    ‖z‖ = 1 / Real.sqrt (p : ℝ) := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (show 0 < p from by omega)
  exact (all_roots_radius_iff (p : ℝ) _ hp₀).mpr
    (CubicHasseBound.paper5_printed_reduction_hasse p hp hA) z hz

end
end ManuscriptAudit.Paper5ActualEulerRadius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper5ActualEulerRadius.actual_reduced_cubic_roots_on_circle
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
