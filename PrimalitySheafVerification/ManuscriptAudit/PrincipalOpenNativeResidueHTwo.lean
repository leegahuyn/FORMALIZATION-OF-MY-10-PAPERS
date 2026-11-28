import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeResidueHTwoOfApproximation
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenEtaleAcyclic

/-! The actual native finite-residue degree-two group vanishes on every
nonempty principal affine open of the affine line. -/

namespace ManuscriptAudit.PrincipalOpenNativeResidueHTwo

open AlgebraicGeometry CategoryTheory
open ProetaleAdicHOneDetection (finiteCoefficient)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

set_option maxHeartbeats 5000000 in
/-- Native residue cohomology of the original polynomial localization. -/
theorem native_HTwo_subsingleton (f : Polynomial K) (hf : f ≠ 0)
    (l r : ℕ) [Fact l.Prime] [NeZero ((l ^ r : ℕ) : K)] :
    Subsingleton (Sheaf.H (finiteCoefficient (PrincipalOpenEtaleAcyclic.U K f) l r) 2) := by
  let E := EtaleBaseChangeFiniteApproximation.principalOpen K f
  exact AffineNativeResidueHTwoOfApproximation.native_residue_HTwo_subsingleton
    (Localization.Away f) E l r
    (PrincipalOpenEtaleAcyclic.cyclic_H_add_two_subsingleton K f hf (l ^ r) 0)

end
end ManuscriptAudit.PrincipalOpenNativeResidueHTwo

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PrincipalOpenNativeResidueHTwo.native_HTwo_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
