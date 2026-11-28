import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineRelativeEtaleCechPositiveOfApproximation

/-! Specialization of actual affine native descent to the affine line. -/

namespace ManuscriptAudit.AffineLineRelativeEtaleCechPositive

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev approximation := EtaleBaseChangeFiniteApproximation.affineLine K

abbrev givenArrow := @AffineRelativeEtaleCechPositiveOfApproximation.givenArrow (Polynomial K) inferInstance

abbrev base_weaklyEtale := @AffineRelativeEtaleCechPositiveOfApproximation.base_weaklyEtale (Polynomial K) inferInstance

abbrev cover_weaklyEtale := @AffineRelativeEtaleCechPositiveOfApproximation.cover_weaklyEtale (Polynomial K) inferInstance

abbrev exactAt_succ := @AffineRelativeEtaleCechPositiveOfApproximation.exactAt_succ (Polynomial K) inferInstance (approximation K)

end
end ManuscriptAudit.AffineLineRelativeEtaleCechPositive

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineRelativeEtaleCechPositive.exactAt_succ] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
