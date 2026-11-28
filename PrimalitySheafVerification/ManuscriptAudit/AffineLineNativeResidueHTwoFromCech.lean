import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineEtaleHTwo
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeResidueHTwoFromCech

/-! The actual affine-line finite-residue vanishing follows from
the actual affine Čech comparison for small étale injectives. -/

namespace ManuscriptAudit.AffineLineNativeResidueHTwoFromCech

open AlgebraicGeometry CategoryTheory Opposite
open EtaleCoefficientUniverseLift (lift)
open EtaleProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open EtaleProetaleAffineLowHTwoFromCech (liftedImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev X := Spec (CommRingCat.of (Polynomial K))
private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev C := Sheaf (X K).smallEtaleTopology A

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero ((ℓ ^ r : ℕ) : K)]

set_option maxHeartbeats 5400000 in
/-- Actual high-universe native residues on the affine line have
zero degree-two cohomology when the actual affine descent inputs hold. -/
theorem native_residue_HTwo_subsingleton
    (hZero : ∀ F : C K, Function.Surjective
      (((adjunction (X K)).unit.app ((lift (X K)).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 (X K))))))
    (hOne : ∀ I : C K, Injective I →
      ProetaleAffineCechHTwo.AffineExactAt (X K) ((liftedImage (X K)).obj I) 1)
    (hTwo : ∀ I : C K, Injective I →
      ProetaleAffineCechHTwo.AffineExactAt (X K) ((liftedImage (X K)).obj I) 2) :
    Subsingleton (Sheaf.H ((ProetaleCoefficientUniverseLift.lift (X K)).obj
      (ProetaleResidueSheaves.residueSheaf (X K) ℓ r)) 2) := 
  AffineNativeResidueHTwoFromCech.native_residue_HTwo_subsingleton (Polynomial K) ℓ r
    (AffineLineEtaleHTwo.cyclic_HTwo_subsingleton K (ℓ ^ r)) hZero hOne hTwo

end
end ManuscriptAudit.AffineLineNativeResidueHTwoFromCech

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineLineNativeResidueHTwoFromCech.native_residue_HTwo_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
