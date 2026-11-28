import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveGenericPoint
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityOpenCover
import PrimalitySheafVerification.ManuscriptAudit.AffineOpenDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.OpenEtalePointSections
import PrimalitySheafVerification.ManuscriptAudit.EtaleTerminalCohomology
import PrimalitySheafVerification.ManuscriptAudit.MayerVietorisHOneVanishing

/-! On the actual projective Weierstrass curve the direct image of the
generic field's unit sheaf has zero first small étale cohomology. -/

namespace ManuscriptAudit.WeierstrassProjectiveGenericUnits

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassProjectiveClosure WeierstrassProjectiveGenericPoint WeierstrassCartierInfinity
open WeierstrassInfinityOpenCover EtaleOpenIntersection KummerUnitsSheaf SmallEtaleBaseChange

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev k := affineOpen W
private abbrev j := neighborhoodOpen W
local instance : IsOpenImmersion (j W) := neighborhoodOpen_isOpenImmersion W

private abbrev l := pullback.fst (j W) (k W) ≫ j W
private abbrev M := fullCoordinateUnitSheaf (genericScheme W)

private abbrev square := EtaleMayerVietoris.openCoverSquare (j W) (k W) (l W)
  (fstLeg (j W) (k W)) (sndLeg (j W) (k W))
  (intersection_isPullback (j W) (k W)) (cover W)

/-- The native direct image of the actual generic-point unit sheaf. -/
def genericUnitImage : Sheaf (projectiveScheme W).smallEtaleTopology AddCommGrpCat.{0} :=
  (directImage (genericPoint W) AddCommGrpCat.{0}).obj (M W)

private def throughOverlap : genericScheme W ⟶ pullback (j W) (k W) :=
  pullback.lift (genericToNeighborhood W) (genericToAffine W)
    (genericPoint_factors_infinity W).symm

private theorem factors_overlap :
    genericPoint W = throughOverlap W ≫ l W := by
  unfold throughOverlap l
  rw [← Category.assoc, pullback.lift_fst]
  exact genericPoint_factors_infinity W

/-- The projective generic-unit direct image has no first cohomology.
This uses native affine direct-image H¹ and the genuine two-open sequence. -/
theorem genericUnitImage_HOne_subsingleton : Subsingleton (Sheaf.H (genericUnitImage W) 1) := by
  have hM : Subsingleton (Sheaf.H (M W) 1) :=
    KummerUnitsSheaf.unitHOne_subsingleton_of_pid W.FunctionField
  have hL : Subsingleton ((genericUnitImage W).H' 1 (Scheme.Etale.mk (j W))) := by
    unfold genericUnitImage
    rw [genericPoint_factors_infinity W]
    exact AffineOpenDirectImageHOne.HOne_subsingleton (genericToNeighborhood W) (j W) (M W) hM
  have hR : Subsingleton ((genericUnitImage W).H' 1 (Scheme.Etale.mk (k W))) :=
    AffineOpenDirectImageHOne.HOne_subsingleton (genericToAffine W) (k W) (M W) hM
  have h0 := (OpenEtalePointSections.restriction_HZero_bijective
    (genericToNeighborhood W) (j W) (l W) (genericPoint W) (throughOverlap W) (M W)
    (fstLeg (j W) (k W)) (genericPoint_factors_infinity W) (factors_overlap W)).2
  have h := MayerVietorisHOneVanishing.subsingleton_HOne (square W) (genericUnitImage W) h0 hL hR
  let e := EtaleTerminalCohomology.terminalHEquiv (projectiveScheme W) (genericUnitImage W) 1
  exact ⟨fun x y => e.symm.injective (h.allEq (e.symm x) (e.symm y))⟩

end

end ManuscriptAudit.WeierstrassProjectiveGenericUnits

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassProjectiveGenericUnits.genericUnitImage_HOne_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
