import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleUnitHOneSquare
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOnePicardBaseChange
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOnePicardAdd
import PrimalitySheafVerification.ManuscriptAudit.AffineEtalePicardEmbeddingIndependence

/-! The actual affine étale unit cohomology injects into the genuine
Picard group, naturally for flat open restriction. -/

namespace ManuscriptAudit.AffineEtaleNativePicardHOne

open AlgebraicGeometry CategoryTheory
open KummerUnitsSheaf AffineEtaleUnitHOneSquare
open AffineEtaleHOneToPicard AffineEtaleHOnePicardAdd AffineEtaleHOnePicardBaseChange
open AffineEtalePicardEmbeddingIndependence AffineEtaleRestrictedResolution
open AffineEtaleOpenRestriction OpenEtaleUnitHOneComposition
open AffineEtaleDerivedRestriction

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

private abbrev X (A : Type) [CommRing A] := Spec (CommRingCat.of A)
private abbrev G (A : Type) [CommRing A] := fullCoordinateUnitSheaf (X A)
private abbrev G' (A : Type) [CommRing A] := coordinateUnitSheaf (X A)
private abbrev m (A : Type) [CommRing A] := Injective.ι (G' A)

variable (A : Type) [CommRing A]

/-- The genuine additive Picard map on actual full small-site unit H¹. -/
def nativePicardHOne : Sheaf.H (G A) 1 →+ Additive (CommRing.Pic A) :=
  (toPicardAdd A (m A)).comp (basisUnitHOne A)

theorem nativePicardHOne_injective : Function.Injective (nativePicardHOne A) :=
  (toPicardAdd_injective A (m A)).comp (basisUnitHOne_bijective A).injective

variable (S : Type) [CommRing S] [Algebra A S] [Module.Flat A S]
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]

/-- Genuine full-site unit pullback commutes with actual scalar extension
of invertible modules in the Picard group. -/
theorem nativePicardHOne_pullback (x : Sheaf.H (G A) 1) :
    (nativePicardHOne S (unitPullback (i A S) x)).toMul =
      CommRing.Pic.mapAlgebra A S (nativePicardHOne A x).toMul := by
  let p := restrictedInjection (i A S) (m A)
  letI : Injective ((affineRestriction (i A S)).obj (Injective.under (G' A))) :=
    restrictedTarget_injective (i A S)
  change toPicard S (m S) (basisUnitHOne S (unitPullback (i A S) x)) =
    CommRing.Pic.mapAlgebra A S (toPicard A (m A) (basisUnitHOne A x))
  rw [basisUnitHOne_square]
  exact (toPicard_independent S (m S) p (restrictHOne A S (basisUnitHOne A x))).trans
    (toPicard_restrict A S (m A) (basisUnitHOne A x))

end

end ManuscriptAudit.AffineEtaleNativePicardHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleNativePicardHOne.nativePicardHOne_injective,
      ``ManuscriptAudit.AffineEtaleNativePicardHOne.nativePicardHOne_pullback] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
