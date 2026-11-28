import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeCechPositiveOfApproximation

/-! Specialization of actual affine native descent to the affine line. -/

namespace ManuscriptAudit.AffineLineNativeCechPositive

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev approximation := EtaleBaseChangeFiniteApproximation.affineLine K

abbrev exactAt_succ := @AffineNativeCechPositiveOfApproximation.exactAt_succ (Polynomial K) inferInstance (approximation K)

end
end ManuscriptAudit.AffineLineNativeCechPositive

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineNativeCechPositive.exactAt_succ] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
