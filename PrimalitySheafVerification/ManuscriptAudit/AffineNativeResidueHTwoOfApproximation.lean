import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeCechPositiveOfApproximation
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeResidueHTwoFromCech
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineProetaleChartTransport

/-! Finite residue coefficients have zero actual degree-two pro-étale
cohomology on an affine base when small étale degree two vanishes. -/

namespace ManuscriptAudit.AffineNativeResidueHTwoOfApproximation

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

variable (R₀ : Type) [CommRing R₀]

private abbrev A := R₀
private abbrev X := Spec (CommRingCat.of (A R₀))

variable (hApprox : EtaleBaseChangeFiniteApproximation.HasWeaklyEtaleApproximations R₀)

include hApprox in
set_option maxHeartbeats 8600000 in
/-- Every positive Čech degree is exact for the native image of a
universe-lifted étale injective on actual affine covering arrows. -/
theorem affine_exactAt_succ
    (I : Sheaf (X R₀).smallEtaleTopology AddCommGrpCat.{0}) [Injective I] (n : ℕ) :
    ProetaleAffineCechHTwo.AffineExactAt (X R₀) ((liftedImage (X R₀)).obj I) (n + 1) := by
  intro V W f hV hW _
  letI := hV
  letI := hW
  let B := coordinateRing W
  let D := coordinateRing V
  let k : B →ₐ[A R₀] D := chartAlgebraMap f
  letI : Algebra B D := k.toRingHom.toAlgebra
  letI : IsScalarTower (A R₀) B D :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (k.commutes a).symm)
  have h : specMap (A R₀) k ≫ structureMap (A R₀) B = structureMap (A R₀) D :=
    ProetaleAffineTensor.specMap_structureMap (A R₀) k
  letI : WeaklyEtale (specMap (A R₀) k ≫ structureMap (A R₀) B) := by rw [h]; infer_instance
  letI : WeaklyEtale (structureMap B D) := WeaklyEtale.of_comp (specMap (A R₀) k) (structureMap (A R₀) B)
  have hE := AffineNativeCechPositiveOfApproximation.exactAt_succ (B := B) (D := D) R₀ hApprox I n
  let e : Arrow.mk (chartMap k) ≅ Arrow.mk f := Arrow.isoMk (chartIso V) (chartIso W)
    (chartIso_natural f).symm
  let P := nativePresheaf ((lift (X R₀)).obj I)
  let j := (NativeCechArrowFunctor.cochains P).mapIso e.symm.op
  exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt j.hom (n + 1)).mp hE

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (ℓ r : ℕ) [Fact ℓ.Prime]

include hApprox in
set_option maxHeartbeats 6300000 in
/-- The actual native pro-étale residue cohomology vanishes in degree
two under the stated prime-to-characteristic condition. -/
theorem native_residue_HTwo_subsingleton
    (hEtale : Subsingleton (Sheaf.H
      ((constantSheaf (X R₀).smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ZMod (ℓ ^ r)))) 2)) :
    Subsingleton (Sheaf.H ((ProetaleCoefficientUniverseLift.lift (X R₀)).obj
      (ProetaleResidueSheaves.residueSheaf (X R₀) ℓ r)) 2) := by
  apply AffineNativeResidueHTwoFromCech.native_residue_HTwo_subsingleton R₀ ℓ r hEtale
  · intro F
    exact AffineNativeRawSectionsOfApproximation.unit_terminal_surjective R₀ hApprox ((lift (X R₀)).obj F)
  · intro I hI
    letI := hI
    exact affine_exactAt_succ R₀ hApprox I 0
  · intro I hI
    letI := hI
    exact affine_exactAt_succ R₀ hApprox I 1

end
end ManuscriptAudit.AffineNativeResidueHTwoOfApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineNativeResidueHTwoOfApproximation.native_residue_HTwo_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
