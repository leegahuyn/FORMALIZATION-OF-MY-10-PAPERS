import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveDegree
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveAffineExact
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityMayerVietoris
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitHOneComposition

/-! For the genuine projective and affine Weierstrass schemes,
the actual open immersion induces an isomorphism on unit Tate modules. -/

namespace ManuscriptAudit.WeierstrassProjectiveActualUnitRestriction

open AlgebraicGeometry CategoryTheory
open KummerUnitsSheaf PowerTateModule
open WeierstrassProjectiveClosure WeierstrassProjectiveDegree
open WeierstrassProjectiveAffineExact WeierstrassInfinityMayerVietoris
open OpenEtaleHOneByRepresentatives OpenEtaleDegreeOnePullback
open OpenEtaleUnitHOneComposition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]
variable (l : ℕ) [Fact l.Prime]

private abbrev F := fullCoordinateUnitSheaf (projectiveScheme W)
private abbrev G := fullCoordinateUnitSheaf (affineScheme W)
private abbrev j := affineOpen W
private abbrev m := Injective.ι (F W)

private def chartCohomologyEquiv :
    (F W).H' 1 (Scheme.Etale.mk (j W)) ≃+ Sheaf.H (G W) 1 :=
  (degreeOneEquiv (j W) (m W)).trans
    (((Sheaf.functorH (affineScheme W).smallEtaleTopology 1).mapIso
      (OpenEtaleUnitComparison.restrictionIso (j W))).addCommGroupIsoToAddEquiv)

/-- Actual restriction along the literal affine open immersion gives a
native p-adic linear equivalence on the Tate modules of unit cohomology. -/
def actualUnitRestrictionTateEquiv :
    Tate l (Sheaf.H (F W) 1) ≃ₗ[ℤ_[l]] Tate l (Sheaf.H (G W) 1) :=
  (mapAddEquiv l (terminalDegreeOneEquiv (m W)).symm).trans
    ((affineRestrictionTateEquiv W (neighborhoodMVRestriction_bijective W)
      (degree W) (degree_boundary W) l).trans (mapAddEquiv l (chartCohomologyEquiv W)))

/-- Its linear map is the actual derived pullback on unit cohomology,
taken on every level of the genuine Tate module. -/
theorem actualUnitRestrictionTateEquiv_apply (x : Tate l (Sheaf.H (F W) 1)) :
    actualUnitRestrictionTateEquiv W l x = map l (unitPullback (j W)) x := by
  apply PowerTateModule.ext l (Sheaf.H (G W) 1)
  intro n
  apply Subtype.ext
  rfl

theorem unitRestrictionTate_bijective :
    Function.Bijective (map l (unitPullback (j W))) := by
  have h : (map l (unitPullback (j W)) : Tate l (Sheaf.H (F W) 1) → Tate l (Sheaf.H (G W) 1)) =
      actualUnitRestrictionTateEquiv W l := funext fun x => (actualUnitRestrictionTateEquiv_apply W l x).symm
  rw [h]
  exact (actualUnitRestrictionTateEquiv W l).bijective

end

end ManuscriptAudit.WeierstrassProjectiveActualUnitRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveActualUnitRestriction.actualUnitRestrictionTateEquiv_apply,
      ``ManuscriptAudit.WeierstrassProjectiveActualUnitRestriction.unitRestrictionTate_bijective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
