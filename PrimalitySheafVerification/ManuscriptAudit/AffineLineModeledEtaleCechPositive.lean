import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineModeledEtaleCechPositiveOfApproximation

/-! Specialization of actual affine native descent to the affine line. -/

namespace ManuscriptAudit.AffineLineModeledEtaleCechPositive

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev approximation := EtaleBaseChangeFiniteApproximation.affineLine K

abbrev arrowFunctor := @AffineModeledEtaleCechPositiveOfApproximation.arrowFunctor (Polynomial K) inferInstance

abbrev arrowCocone := @AffineModeledEtaleCechPositiveOfApproximation.arrowCocone (Polynomial K) inferInstance

abbrev limit_base_weaklyEtale := @AffineModeledEtaleCechPositiveOfApproximation.limit_base_weaklyEtale (Polynomial K) inferInstance

abbrev limit_cover_weaklyEtale := @AffineModeledEtaleCechPositiveOfApproximation.limit_cover_weaklyEtale (Polynomial K) inferInstance

abbrev exactAt_succ := @AffineModeledEtaleCechPositiveOfApproximation.exactAt_succ (Polynomial K) inferInstance (approximation K)

end
end ManuscriptAudit.AffineLineModeledEtaleCechPositive

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineModeledEtaleCechPositive.exactAt_succ] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
