import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleUnitsHTwo
import PrimalitySheafVerification.ManuscriptAudit.RatFuncFiniteGaloisUnitCohomology

/-! The unit sheaf of the rational function field over an algebraically closed field has H² zero. -/

namespace ManuscriptAudit.RatFuncTsen

open AlgebraicGeometry CategoryTheory KummerUnitsSheaf

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

theorem rationalFunction_etale_units_HTwo_subsingleton (K : Type) [Field K] [IsAlgClosed K] :
    Subsingleton (Sheaf.H
      (fullCoordinateUnitSheaf (Spec (CommRingCat.of (RatFunc K)))) 2) := by
  apply FieldEtaleUnitsHTwo.unitSheaf_HTwo_subsingleton_of_finiteGalois
  intro L _ _ _ _
  exact rationalFunction_finiteGalois_units_HTwo_subsingleton K L

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RatFuncTsen.rationalFunction_etale_units_HTwo_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
