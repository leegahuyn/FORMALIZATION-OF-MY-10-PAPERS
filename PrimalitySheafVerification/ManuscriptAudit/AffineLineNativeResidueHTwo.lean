import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeResidueHTwoOfApproximation
import PrimalitySheafVerification.ManuscriptAudit.AffineLineEtaleHTwo

/-! Finite residue coefficients have zero actual degree-two pro-étale
cohomology on the affine line over an algebraically closed field. -/

namespace ManuscriptAudit.AffineLineNativeResidueHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap specMap)
open NativeAffineProetaleChartTransport (coordinateRing chartIso chartAlgebraMap chartIso_natural)
open NativeAffineEtaleRawStageElements (chartMap)
open NativeCechNerve (Cech)
open NativeAffineCechRawComparison (nativePresheaf)
open EtaleCoefficientUniverseLift (lift)
open EtaleProetaleAffineLowHTwoFromCech (liftedImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := Polynomial K
private abbrev X := Spec (CommRingCat.of (A K))

/-- Exactness on the genuine affine covers of the affine line. -/
abbrev affine_exactAt_succ := @AffineNativeResidueHTwoOfApproximation.affine_exactAt_succ
  (Polynomial K) inferInstance (EtaleBaseChangeFiniteApproximation.affineLine K)

variable (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero ((ℓ ^ r : ℕ) : K)]

set_option maxHeartbeats 6300000 in
/-- The actual native pro-étale residue cohomology vanishes in degree
two under the stated prime-to-characteristic condition. -/
theorem native_residue_HTwo_subsingleton :
    Subsingleton (Sheaf.H ((ProetaleCoefficientUniverseLift.lift (X K)).obj
      (ProetaleResidueSheaves.residueSheaf (X K) ℓ r)) 2)  :=
  AffineNativeResidueHTwoOfApproximation.native_residue_HTwo_subsingleton
    (Polynomial K) (EtaleBaseChangeFiniteApproximation.affineLine K) ℓ r
    (AffineLineEtaleHTwo.cyclic_HTwo_subsingleton K (ℓ ^ r))

end
end ManuscriptAudit.AffineLineNativeResidueHTwo

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineLineNativeResidueHTwo.native_residue_HTwo_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
