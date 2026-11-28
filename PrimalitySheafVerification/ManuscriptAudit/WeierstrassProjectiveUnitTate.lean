import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveDegree
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveAffineExact
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityMayerVietoris
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineOpenDivisorHOne

/-! The Tate module of genuine projective étale unit cohomology is the
native geometric elliptic-curve Tate module. -/

namespace ManuscriptAudit.WeierstrassProjectiveUnitTate

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassProjectiveGenericQuotient
open WeierstrassProjectiveAffineExact WeierstrassProjectiveDegree
open WeierstrassInfinityMayerVietoris WeierstrassAffineOpenDivisorHOne
open PowerTateModule KummerUnitsSheaf EtaleTerminalCohomology

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]
variable (l : ℕ) [Fact l.Prime]

/-- On native projective unit cohomology, affine restriction followed by
the usual point–divisor correspondence identifies the integral Tate module. -/
def unitTateEquiv :
    Tate l (Sheaf.H (fullCoordinateUnitSheaf (projectiveScheme W)) 1) ≃ₗ[ℤ_[l]] Tate l W.Point := by
  let e := terminalHEquiv (projectiveScheme W) (fullCoordinateUnitSheaf (projectiveScheme W)) 1
  exact (mapAddEquiv l e.symm).trans
    ((affineRestrictionTateEquiv W (neighborhoodMVRestriction_bijective W)
      (degree W) (degree_boundary W) l).trans (mapAddEquiv l (affineHOnePointEquiv W)))

end

end ManuscriptAudit.WeierstrassProjectiveUnitTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassProjectiveUnitTate.unitTateEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
