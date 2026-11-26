import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.Exact
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitMono

/-!
# The generic-point unit quotient on the full small étale site

The cokernel of regular units in the actual generic-point direct image
belongs to a native short exact sequence of étale sheaves.
-/

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

private theorem cokernelSequence_shortExact {C : Type*} [Category* C] [Abelian C]
    {U V : C} (f : U ⟶ V) (hf : Mono f) : (ShortComplex.cokernelSequence f).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f) hf inferInstance

variable (A F : Type) [CommRing A] [IsDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F]

/-- The quotient of generic-point units by regular units, formed in étale sheaves. -/
abbrev genericPointUnitQuotient :
    Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{0} :=
  cokernel (genericPointUnitsHom A F)

/-- The native generic-point unit sequence on the full small étale site. -/
def genericPointUnitSequence :
    ShortComplex (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{0}) :=
  ShortComplex.cokernelSequence (genericPointUnitsHom A F)

/-- The generic-point unit sequence is short exact. -/
theorem genericPointUnitSequence_shortExact : (genericPointUnitSequence A F).ShortExact :=
  cokernelSequence_shortExact (genericPointUnitsHom A F) (genericPointUnitsHom_mono A F)

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.GenericEtaleUnitSections.genericPointUnitSequence_shortExact
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
