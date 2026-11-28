import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeRawSectionsOfApproximation

/-! Specialization of actual affine native descent to the affine line. -/

namespace ManuscriptAudit.AffineLineNativeRawSections

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev approximation := EtaleBaseChangeFiniteApproximation.affineLine K

abbrev finite_approximation := @AffineNativeRawSectionsOfApproximation.finite_approximation (Polynomial K) inferInstance (approximation K)

abbrev comparison_bijective := @AffineNativeRawSectionsOfApproximation.comparison_bijective (Polynomial K) inferInstance (approximation K)

abbrev unit_terminal_surjective := @AffineNativeRawSectionsOfApproximation.unit_terminal_surjective (Polynomial K) inferInstance (approximation K)

abbrev isColimit_native := @AffineNativeRawSectionsOfApproximation.isColimit_native (Polynomial K) inferInstance (approximation K)

end
end ManuscriptAudit.AffineLineNativeRawSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineNativeRawSections.comparison_bijective,
      ``ManuscriptAudit.AffineLineNativeRawSections.unit_terminal_surjective,
      ``ManuscriptAudit.AffineLineNativeRawSections.isColimit_native] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
