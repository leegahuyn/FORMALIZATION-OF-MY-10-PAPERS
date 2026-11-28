import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleNestedUnitRestriction
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityPunctureHOne
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityOpenCover

/-! The infinity-chart arm of the literal projective Mayer–Vietoris
sequence is bijective on the genuine first étale unit cohomology. -/

namespace ManuscriptAudit.WeierstrassInfinityMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open WeierstrassCartierInfinity WeierstrassInfinityChartAlgebra
open WeierstrassInfinityOpenCover WeierstrassProjectiveClosure
open WeierstrassInfinityPunctureHOne AffineEtaleNestedUnitRestriction
open EtaleOpenIntersection KummerUnitsSheaf NestedOpenEtaleSectionNaturality

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev j := neighborhoodOpen W
private abbrev k := affineOpen W
private abbrev i := punctureToNeighborhood W
private abbrev F := fullCoordinateUnitSheaf (projectiveScheme W)

local instance : IsOpenImmersion (j W) := neighborhoodOpen_isOpenImmersion W

private def etaleOverlapIso :
    Scheme.Etale.mk (pullback.fst (j W) (k W) ≫ j W) ≅ Scheme.Etale.mk (i W ≫ j W) :=
  MorphismProperty.Over.isoMk (overlapIso W) (by
    rw [← Category.assoc, overlapIso_fac])

private theorem canonical_leftLeg :
    (etaleOverlapIso W).hom ≫ nestedObjectArrow (i W) (j W) = fstLeg (j W) (k W) := by
  apply MorphismProperty.Over.Hom.ext
  exact overlapIso_fac W

/-- Restriction from the actual infinity neighborhood to the left arm of
the literal two-open cover induces an isomorphism on first unit cohomology. -/
theorem neighborhoodMVRestriction_bijective :
    Function.Bijective (((F W).cohomologyPresheaf 1).map (fstLeg (j W) (k W)).op).hom := by
  let f := (F W).cohomologyPresheaf 1
  let e := (f.mapIso (etaleOverlapIso W).op).addCommGroupIsoToAddEquiv
  have h : Function.Bijective (f.map (nestedObjectArrow (i W) (j W)).op).hom := by
    exact ambientRestriction_bijective (Neighborhood W) (Puncture W) (j W)
      (neighborhood_HOne_to_puncture_bijective W)
  rw [← canonical_leftLeg W, op_comp, Functor.map_comp]
  exact e.bijective.comp h

end

end ManuscriptAudit.WeierstrassInfinityMayerVietoris

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassInfinityMayerVietoris.neighborhoodMVRestriction_bijective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
