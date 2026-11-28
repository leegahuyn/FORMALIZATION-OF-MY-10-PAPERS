import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOnePicard
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleHOnePicardBaseChange
import PrimalitySheafVerification.ManuscriptAudit.DedekindPicardLocalization
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityDedekind
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityOpenCover

/-! Restricting actual affine unit cohomology from the infinity chart
to its native puncture is an isomorphism, since the deleted prime is principal. -/

namespace ManuscriptAudit.WeierstrassInfinityPunctureHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AffineEtaleOpenRestriction AffineEtaleRestrictedResolution
open AffineEtaleDerivedRestriction AffineEtaleHOnePicardBaseChange
open AffineEtaleHOneToPicard AffineEtaleHOnePicard AffineEtaleHOnePicardAdd
open KummerUnitsSheaf WeierstrassInfinityChartAlgebra WeierstrassInfinityPuncture WeierstrassInfinityOpenCover

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S] [Module.Flat A S]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev J (R : Type) [CommRing R] := Scheme.AffineEtale.topology (X R)
private abbrev C (R : Type) [CommRing R] := Sheaf (J R) AddCommGrpCat.{0}
private abbrev G (R : Type) [CommRing R] := coordinateUnitSheaf (X R)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (j A S)]

/-- Actual affine étale H¹ restriction is an isomorphism whenever the
same native scalar extension is bijective on Picard groups. -/
theorem restriction_bijective_of_picard
    (h : Function.Bijective (CommRing.Pic.mapAlgebra A S)) :
    Function.Bijective (restrictHOne A S) := by
  letI : IsGrothendieckAbelian.{0} (C A) :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology (X A) AddCommGrpCat.{0}
  letI : EnoughInjectives (C A) := IsGrothendieckAbelian.enoughInjectives.{0} (C := C A)
  let i := Injective.ι (G A)
  let I := Injective.under (G A)
  let r := restrictedInjection (j A S) i
  letI : Injective ((affineRestriction (j A S)).obj I) := restrictedTarget_injective (j A S)
  have hI : Function.Injective (toPicard A i) := by
    intro a b e
    apply toPicardAdd_injective A i
    exact congrArg Additive.ofMul e
  have hS : Function.Injective (toPicard S r) := by
    intro a b e
    apply toPicardAdd_injective S r
    exact congrArg Additive.ofMul e
  constructor
  · intro x y hxy
    apply hI
    apply h.1
    rw [← toPicard_restrict A S i x, ← toPicard_restrict A S i y, hxy]
  · intro y
    obtain ⟨P, hP⟩ := h.2 (toPicard S r y)
    obtain ⟨x, hx⟩ := toPicard_surjective A i P
    refine ⟨x, hS ?_⟩
    rw [toPicard_restrict A S i x, hx, hP]

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

/-- The literal puncture at the unique Cartier point preserves the
native affine Picard group. -/
theorem neighborhood_picard_to_puncture_bijective :
    Function.Bijective (CommRing.Pic.mapAlgebra (Neighborhood W) (Puncture W)) := by
  letI : IsDedekindDomain (Neighborhood W) :=
    WeierstrassInfinityDedekind.neighborhood_isDedekindDomain W
  exact DedekindPicardLocalization.mapAlgebra_bijective (localX W) (localX_prime W)

/-- The native first unit-cohomology restriction of the infinity
neighborhood to its genuine open overlap is bijective. -/
theorem neighborhood_HOne_to_puncture_bijective :
    Function.Bijective (restrictHOne (Neighborhood W) (Puncture W)) := by
  apply restriction_bijective_of_picard
  exact neighborhood_picard_to_puncture_bijective W

end

end ManuscriptAudit.WeierstrassInfinityPunctureHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityPunctureHOne.restriction_bijective_of_picard,
      ``ManuscriptAudit.WeierstrassInfinityPunctureHOne.neighborhood_picard_to_puncture_bijective,
      ``ManuscriptAudit.WeierstrassInfinityPunctureHOne.neighborhood_HOne_to_puncture_bijective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
