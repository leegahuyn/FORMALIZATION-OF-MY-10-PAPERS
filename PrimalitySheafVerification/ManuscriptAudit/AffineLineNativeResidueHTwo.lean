import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineNativeCechPositive
import PrimalitySheafVerification.ManuscriptAudit.AffineLineNativeResidueHTwoFromCech
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineProetaleChartTransport

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

set_option maxHeartbeats 8600000 in
/-- Every positive Čech degree is exact for the native image of a
universe-lifted étale injective on actual affine covering arrows. -/
theorem affine_exactAt_succ
    (I : Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}) [Injective I] (n : ℕ) :
    ProetaleAffineCechHTwo.AffineExactAt (X K) ((liftedImage (X K)).obj I) (n + 1) := by
  intro V W f hV hW _
  letI := hV
  letI := hW
  let B := coordinateRing W
  let D := coordinateRing V
  let k : B →ₐ[A K] D := chartAlgebraMap f
  letI : Algebra B D := k.toRingHom.toAlgebra
  letI : IsScalarTower (A K) B D :=
    IsScalarTower.of_algebraMap_eq (fun a ↦ (k.commutes a).symm)
  have h : specMap (A K) k ≫ structureMap (A K) B = structureMap (A K) D :=
    ProetaleAffineTensor.specMap_structureMap (A K) k
  letI : WeaklyEtale (specMap (A K) k ≫ structureMap (A K) B) := by rw [h]; infer_instance
  letI : WeaklyEtale (structureMap B D) := WeaklyEtale.of_comp (specMap (A K) k) (structureMap (A K) B)
  have hE := AffineLineNativeCechPositive.exactAt_succ (B := B) (D := D) K I n
  let e : Arrow.mk (chartMap k) ≅ Arrow.mk f := Arrow.isoMk (chartIso V) (chartIso W)
    (chartIso_natural f).symm
  let P := nativePresheaf ((lift (X K)).obj I)
  let j := (NativeCechArrowFunctor.cochains P).mapIso e.symm.op
  exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt j.hom (n + 1)).mp hE

variable (ℓ r : ℕ) [Fact ℓ.Prime] [NeZero ((ℓ ^ r : ℕ) : K)]

set_option maxHeartbeats 6300000 in
/-- The actual native pro-étale residue cohomology vanishes in degree
two under the stated prime-to-characteristic condition. -/
theorem native_residue_HTwo_subsingleton :
    Subsingleton (Sheaf.H ((ProetaleCoefficientUniverseLift.lift (X K)).obj
      (ProetaleResidueSheaves.residueSheaf (X K) ℓ r)) 2) := by
  apply AffineLineNativeResidueHTwoFromCech.native_residue_HTwo_subsingleton K ℓ r
  · intro F
    exact AffineLineNativeRawSections.unit_terminal_surjective K ((lift (X K)).obj F)
  · intro I hI
    letI := hI
    exact affine_exactAt_succ K I 0
  · intro I hI
    letI := hI
    exact affine_exactAt_succ K I 1

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
