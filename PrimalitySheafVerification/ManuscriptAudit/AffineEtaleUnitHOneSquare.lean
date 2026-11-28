import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleBasisHOne
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleUnitSiteSquare
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitHOneComposition

/-! The actual full-site unit pullback and actual affine-basis unit
restriction give the identical degree-one map through their comparison. -/

namespace ManuscriptAudit.AffineEtaleUnitHOneSquare

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open KummerUnitsSheaf OpenEtaleExtension OpenEtaleUnitHOneComposition
open OpenEtaleDegreeOneComposition OpenEtaleDegreeOneExt
open AffineEtaleBasisHOne AffineEtaleUnitSiteSquare AffineEtaleConstantRestrictionSquare
open AffineEtaleOpenRestriction AffineEtaleRestrictedUnits AffineEtaleDerivedRestriction

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

private abbrev B := AddCommGrpCat.{0}
private abbrev X (A : Type) [CommRing A] := Spec (CommRingCat.of A)
private abbrev G (A : Type) [CommRing A] := fullCoordinateUnitSheaf (X A)
private abbrev G' (A : Type) [CommRing A] := coordinateUnitSheaf (X A)
private abbrev Jb (A : Type) [CommRing A] := Scheme.AffineEtale.topology (X A)
private abbrev E (A : Type) [CommRing A] := Scheme.AffineEtale.sheafEquiv (X A) B
private abbrev b (A : Type) [CommRing A] := (basisUnitsIso (X A)).hom

variable (A : Type) [CommRing A]

/-- The genuine affine-basis comparison for unit cohomology. -/
def basisUnitHOne : Sheaf.H (G A) 1 →+ Sheaf.H (G' A) 1 :=
  (Sheaf.H.map (b A) 1).comp (basisHOneMap A (G A))

theorem basisUnitHOne_bijective : Function.Bijective (basisUnitHOne A) := by
  let e := (((Sheaf.functorH (Jb A) 1).mapIso (basisUnitsIso (X A))).addCommGroupIsoToAddEquiv)
  exact e.bijective.comp (basisHOneMap_bijective A (G A))

variable (S : Type) [CommRing S] [Algebra A S]
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]
private abbrev R := affineRestriction (i A S)
private abbrev u := (OpenEtaleUnitComparison.restrictionIso (i A S)).hom
private abbrev v := (restrictionUnitsIso (i A S)).hom

local instance : PreservesFiniteLimits (R A S) := (affineRestriction_exact (i A S)).1
local instance : PreservesFiniteColimits (R A S) := (affineRestriction_exact (i A S)).2
local instance : (R A S).Additive := (R A S).additive_of_preserves_binary_products

private theorem affineExt_units (x : Sheaf.H (G' A) 1) :
    Sheaf.H.map (v A S) 1 (affineExtPullback A S (G' A) x) = restrictHOne A S x := by
  let z := Ext.mk₀ (restrictionConstant A S)
  let x' := x.mapExactFunctor (R A S)
  change (z.comp x' (zero_add 1)).comp (Ext.mk₀ (v A S)) (add_zero 1) =
    z.comp (x'.comp (Ext.mk₀ (v A S)) (add_zero 1)) (zero_add 1)
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ _

/-- Under the actual affine-basis comparison, genuine full-site pullback
is exactly the native affine unit cohomology pullback used for Picard. -/
theorem basisUnitHOne_square (x : Sheaf.H (G A) 1) :
    basisUnitHOne S (unitPullback (i A S) x) =
      restrictHOne A S (basisUnitHOne A x) := by
  change Sheaf.H.map (b S) 1
    (basisHOneMap S (G S) (Sheaf.H.map (u A S) 1
      (OpenEtaleDegreeOneCoefficients.pullback (i A S) (G A) x))) =
    restrictHOne A S (Sheaf.H.map (b A) 1 (basisHOneMap A (G A) x))
  rw [basisHOneMap_coeff, ← extPullback_eq, ← basisHOne_square,
    ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, ← unit_square,
    Sheaf.H.map_comp_apply, ← affineExtPullback_coeff]
  exact affineExt_units A S (Sheaf.H.map (b A) 1 (basisHOneMap A (G A) x))

end

end ManuscriptAudit.AffineEtaleUnitHOneSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleUnitHOneSquare.basisUnitHOne_bijective,
      ``ManuscriptAudit.AffineEtaleUnitHOneSquare.basisUnitHOne_square] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
