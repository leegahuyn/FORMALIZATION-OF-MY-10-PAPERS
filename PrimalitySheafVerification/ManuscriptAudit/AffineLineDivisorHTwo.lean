import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorFullExact
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHOne
import PrimalitySheafVerification.ManuscriptAudit.SheafShortExactSections

/-!
# Restriction to the generic point in degree two

The actual affine-line divisor sequence and vanishing of degree-one
divisor cohomology show that the unit-sheaf degree-two class injects
into the degree-two cohomology of the generic-point direct image.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory
open GenericEtaleUnitSections

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K F : Type) [Field K] [IsAlgClosed K] [Field F]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical regular-to-generic unit map is injective on H². -/
theorem regularUnits_HTwo_map_injective :
    Function.Injective (Sheaf.H.map (genericPointUnitsHom (Polynomial K) F) 2) :=
  SheafShortExactSections.HTwo_map_injective_of_HOne
    (divisorSequence K F) (divisorSequence_shortExact K F) (divisor_HOne_subsingleton K)

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineLineDivisorSheaf.regularUnits_HTwo_map_injective
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
