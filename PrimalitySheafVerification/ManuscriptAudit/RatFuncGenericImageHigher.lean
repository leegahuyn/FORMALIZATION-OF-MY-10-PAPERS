import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleAcyclicCohomology
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitSections
import PrimalitySheafVerification.ManuscriptAudit.RatFuncEtaleUnitsHigher

/-! Actual generic-unit direct images for the affine line have no positive cohomology. -/

namespace ManuscriptAudit.RatFuncTsen

open AlgebraicGeometry CategoryTheory GenericEtaleUnitSections

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

/-- For any integrally closed domain with fraction field K(t), the
native generic-unit direct image has no positive étale cohomology. -/
theorem genericUnitImage_H_succ_subsingleton (K A : Type) [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A (RatFunc K)] [IsFractionRing A (RatFunc K)] (n : ℕ) :
    Subsingleton (Sheaf.H (genericUnitImage A (RatFunc K)) (n + 1)) :=
  GenericEtaleAcyclicSections.directImage_H_succ_subsingleton A (RatFunc K) _
    (finiteExtension_etale_units_hasAcyclicGaloisSections K (RatFunc K)) n

/-- The direct image of the unit sheaf from the actual generic point
of the affine line has zero positive-degree cohomology. -/
theorem affineLine_genericUnitImage_H_succ_subsingleton (K : Type) [Field K] [IsAlgClosed K]
    (n : ℕ) :
    Subsingleton (Sheaf.H (genericUnitImage (Polynomial K) (RatFunc K)) (n + 1)) :=
  genericUnitImage_H_succ_subsingleton K (Polynomial K) n

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.RatFuncTsen.affineLine_genericUnitImage_H_succ_subsingleton
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
